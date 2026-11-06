"""Open a built kernel image for scraping, without booting it.

Every scraper here used to read the *running* kernel through
`drgn.program_from_kernel()`, which needs root and, worse, describes whatever
kernel the host happens to boot rather than the one this repo vendors and runs
in its VM. Every BTF id that reached `policy.json` therefore belonged to the
wrong kernel.

Almost everything the scrapers want is static initialised data: a
`struct bpf_func_proto` is a `const` object in `.rodata`, and the kfunc id sets
are `BTF_ID_FLAGS` rows that `resolve_btfids` patches at build time. All of it
sits in the `vmlinux` ELF. [`open_program`] therefore hands drgn the ELF's
`PT_LOAD` segments as its memory, so `prog['bpf_map_lookup_elem_proto']` reads
exactly what the linker wrote. No root, no live kernel, and the answers describe
the vendored build.

What this *cannot* give you is runtime state: anything a boot-time initialiser
or a module registration writes is still zero here. `btf_vmlinux`, for one, is
null, so BTF type names must come from the image's own `.BTF` section instead
(see [`btf`](btf.py)).
"""

from __future__ import annotations

import re
import struct
from dataclasses import dataclass
from pathlib import Path

import drgn

# Default location of the vendored kernel build, relative to this file:
# policy_emitter/scrapers -> repo root -> .vm/linux-build/<arch>/vmlinux.
_REPO_ROOT = Path(__file__).resolve().parents[2]
_BUILD_ROOT = _REPO_ROOT / ".vm" / "linux-build"

# ELF constants we need; the kernel image is always ELF64 little-endian on the
# architectures this repo builds for.
_PT_LOAD = 1
_SHT_SYMTAB = 2


@dataclass(frozen=True)
class Segment:
    """One `PT_LOAD` program header."""

    vaddr: int
    memsz: int
    offset: int
    filesz: int


class Vmlinux:
    """A built kernel image, opened for reading."""

    def __init__(self, path: Path) -> None:
        self.path = Path(path)
        self.data = self.path.read_bytes()
        self.segments = _load_segments(self.data)
        if not self.segments:
            raise ValueError(f"{self.path} has no PT_LOAD segments; not a kernel image")

    def section(self, name: str) -> bytes | None:
        """Raw contents of a named section, or `None` if the image lacks it."""
        return _section_data(self.data, name)

    def release(self) -> str:
        """The kernel release string (`uname -r`) this image was built as.

        Read out of `.rodata`'s `linux_banner`, which is the one place the
        version survives into the image verbatim. Used only to stamp provenance
        onto the scraped JSON, so a miss is not fatal.
        """
        match = re.search(rb"Linux version ([^\s]+) ", self.data)
        return match.group(1).decode() if match else "unknown"

    def build_id(self) -> str:
        """The GNU build id, so two scrapes can be checked to share an image."""
        note = _section_data(self.data, ".notes") or _section_data(self.data, ".note.gnu.build-id")
        if not note:
            return "unknown"
        # Walk the note section for NT_GNU_BUILD_ID (type 3, owner "GNU").
        offset = 0
        while offset + 12 <= len(note):
            namesz, descsz, ntype = struct.unpack_from("<III", note, offset)
            name_start = offset + 12
            desc_start = name_start + ((namesz + 3) & ~3)
            end = desc_start + ((descsz + 3) & ~3)
            if ntype == 3 and note[name_start : name_start + namesz] == b"GNU\0":
                return note[desc_start : desc_start + descsz].hex()
            if end <= offset:
                break
            offset = end
        return "unknown"

    def program(self) -> drgn.Program:
        """A drgn program reading this image's static data.

        The ELF's own load segments serve as memory, so any object the linker
        initialised reads back exactly as built. Objects a boot-time initialiser
        would fill are zero, which is the honest answer: this image has not run.
        """
        prog = drgn.Program(drgn.Platform(_architecture(self.data)))
        for segment in self.segments:
            prog.add_memory_segment(
                segment.vaddr, segment.memsz, _reader(self.data, segment)
            )
        module = prog.extra_module("vmlinux", create=True)
        module.address_range = (
            min(s.vaddr for s in self.segments),
            max(s.vaddr + s.memsz for s in self.segments),
        )
        module.try_file(str(self.path), force=True)
        if module.debug_file_status != drgn.ModuleFileStatus.HAVE:
            raise ValueError(
                f"{self.path} carries no usable DWARF; build the kernel with "
                "CONFIG_DEBUG_INFO"
            )
        return prog


def default_path() -> Path:
    """The vendored kernel build, whichever architecture was built."""
    candidates = sorted(_BUILD_ROOT.glob("*/vmlinux"))
    # `arm64` / `amd64` before `arm64-stock`: the stock build is the comparison
    # kernel, never the one the policy describes.
    for candidate in candidates:
        if not candidate.parent.name.endswith("-stock"):
            return candidate
    if candidates:
        return candidates[0]
    return _BUILD_ROOT / "arm64" / "vmlinux"


def add_argument(parser) -> None:
    """Adds the shared `--vmlinux` option to a scraper's argument parser."""
    parser.add_argument(
        "--vmlinux",
        type=Path,
        default=None,
        help="Built vendored kernel image to scrape (default: the newest build "
        "under .vm/linux-build). Run `just linux-build` first.",
    )


def open_from_args(args) -> Vmlinux:
    """Opens the image `--vmlinux` names, with a pointed error if it is absent."""
    path = args.vmlinux or default_path()
    if not path.exists():
        raise SystemExit(
            f"kernel image not found: {path}\n"
            "       run `just linux-build`, or pass --vmlinux"
        )
    return Vmlinux(path)


def provenance(image: Vmlinux) -> dict:
    """The stamp every scraped JSON carries, so a mixed set can be detected."""
    return {
        "kernel_release": image.release(),
        "build_id": image.build_id(),
    }


def _architecture(data: bytes) -> drgn.Architecture:
    machine, = struct.unpack_from("<H", data, 18)
    return {0xB7: drgn.Architecture.AARCH64, 0x3E: drgn.Architecture.X86_64}.get(
        machine, drgn.Architecture.UNKNOWN
    )


def _load_segments(data: bytes) -> list[Segment]:
    e_phoff, = struct.unpack_from("<Q", data, 32)
    e_phentsize, e_phnum = struct.unpack_from("<HH", data, 54)
    out = []
    for i in range(e_phnum):
        base = e_phoff + i * e_phentsize
        p_type, = struct.unpack_from("<I", data, base)
        if p_type != _PT_LOAD:
            continue
        p_offset, p_vaddr = struct.unpack_from("<QQ", data, base + 8)
        p_filesz, p_memsz = struct.unpack_from("<QQ", data, base + 32)
        out.append(Segment(p_vaddr, p_memsz, p_offset, p_filesz))
    return out


def _reader(data: bytes, segment: Segment):
    def read(address, count, offset, physical):  # noqa: ARG001 (drgn's signature)
        start = segment.offset + (address - segment.vaddr)
        # Bytes past `filesz` are `.bss`: zero in the image, and zero at boot
        # until something writes them.
        available = max(0, min(count, segment.offset + segment.filesz - start))
        return data[start : start + available].ljust(count, b"\0")

    return read


def _section_data(data: bytes, name: str) -> bytes | None:
    e_shoff, = struct.unpack_from("<Q", data, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    strtab_base = e_shoff + e_shstrndx * e_shentsize
    str_off, str_size = struct.unpack_from("<QQ", data, strtab_base + 24)
    names = data[str_off : str_off + str_size]
    target = name.encode()
    for i in range(e_shnum):
        base = e_shoff + i * e_shentsize
        sh_name, = struct.unpack_from("<I", data, base)
        end = names.index(b"\0", sh_name)
        if names[sh_name:end] != target:
            continue
        sh_offset, sh_size = struct.unpack_from("<QQ", data, base + 24)
        return data[sh_offset : sh_offset + sh_size]
    return None
