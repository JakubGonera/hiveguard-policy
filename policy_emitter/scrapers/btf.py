"""Read a kernel image's `.BTF` section.

The scrapers need to turn BTF type ids into names, and to read function
prototypes out of struct members. On a running kernel that is a walk of the
`btf_vmlinux` object; in a built image that object is null, because nothing has
booted to parse the section. The section itself is right there, so parse it.

Only what the scrapers ask for is modelled: names, the pointer/qualifier chain,
struct members, and function prototypes. The binary layout is
`include/uapi/linux/btf.h`.
"""

from __future__ import annotations

import struct
from dataclasses import dataclass

BTF_MAGIC = 0xEB9F

# `BTF_KIND_*`, in the order the uapi header declares them.
(
    KIND_VOID,
    KIND_INT,
    KIND_PTR,
    KIND_ARRAY,
    KIND_STRUCT,
    KIND_UNION,
    KIND_ENUM,
    KIND_FWD,
    KIND_TYPEDEF,
    KIND_VOLATILE,
    KIND_CONST,
    KIND_RESTRICT,
    KIND_FUNC,
    KIND_FUNC_PROTO,
    KIND_VAR,
    KIND_DATASEC,
    KIND_FLOAT,
    KIND_DECL_TAG,
    KIND_TYPE_TAG,
    KIND_ENUM64,
) = range(20)

# Kinds that wrap another type without changing what it *is*, so resolving a
# type to its underlying struct walks straight through them.
_TRANSPARENT = frozenset({KIND_CONST, KIND_VOLATILE, KIND_RESTRICT, KIND_TYPEDEF, KIND_TYPE_TAG})

# Extra bytes each kind carries after the common 12-byte header, as a function
# of `vlen`.
_TRAILING = {
    KIND_INT: lambda vlen: 4,
    KIND_ARRAY: lambda vlen: 12,
    KIND_STRUCT: lambda vlen: 12 * vlen,
    KIND_UNION: lambda vlen: 12 * vlen,
    KIND_ENUM: lambda vlen: 8 * vlen,
    KIND_FUNC_PROTO: lambda vlen: 8 * vlen,
    KIND_VAR: lambda vlen: 4,
    KIND_DATASEC: lambda vlen: 12 * vlen,
    KIND_DECL_TAG: lambda vlen: 4,
    KIND_ENUM64: lambda vlen: 12 * vlen,
}


@dataclass(frozen=True)
class Member:
    """One struct or union member."""

    name: str
    type_id: int
    bits_offset: int


@dataclass(frozen=True)
class Param:
    """One function-prototype parameter."""

    name: str
    type_id: int


@dataclass(frozen=True)
class Type:
    """One BTF type."""

    id: int
    kind: int
    name: str
    size: int
    """`size` for sized kinds, the referenced type id for the rest."""
    members: tuple[Member, ...] = ()
    params: tuple[Param, ...] = ()

    @property
    def ref(self) -> int:
        """The type this one refers to (pointers, qualifiers, prototypes' return)."""
        return self.size


class Btf:
    """A parsed `.BTF` section."""

    def __init__(self, blob: bytes) -> None:
        magic, version, _flags, hdr_len = struct.unpack_from("<HBBI", blob, 0)
        if magic != BTF_MAGIC:
            raise ValueError(f"not a BTF blob: magic {magic:#x}")
        if version != 1:
            raise ValueError(f"unsupported BTF version {version}")
        type_off, type_len, str_off, str_len = struct.unpack_from("<IIII", blob, 8)
        self._strings = blob[hdr_len + str_off : hdr_len + str_off + str_len]
        self.types: list[Type] = [Type(0, KIND_VOID, "void", 0)]
        self._parse_types(blob, hdr_len + type_off, type_len)
        self._by_name: dict[tuple[int, str], Type] = {}
        for ty in self.types:
            if ty.name:
                self._by_name.setdefault((ty.kind, ty.name), ty)

    def _parse_types(self, blob: bytes, start: int, length: int) -> None:
        pos = start
        end = start + length
        while pos < end:
            name_off, info, size = struct.unpack_from("<III", blob, pos)
            vlen = info & 0xFFFF
            kind = (info >> 24) & 0x1F
            body = pos + 12
            members: tuple[Member, ...] = ()
            params: tuple[Param, ...] = ()
            if kind in (KIND_STRUCT, KIND_UNION):
                members = tuple(
                    Member(
                        self._string(m_name),
                        m_type,
                        # A bitfield struct packs the offset with the bit size;
                        # the low 24 bits are the offset either way.
                        m_off & 0xFFFFFF,
                    )
                    for m_name, m_type, m_off in struct.iter_unpack(
                        "<III", blob[body : body + 12 * vlen]
                    )
                )
            elif kind == KIND_FUNC_PROTO:
                params = tuple(
                    Param(self._string(p_name), p_type)
                    for p_name, p_type in struct.iter_unpack(
                        "<II", blob[body : body + 8 * vlen]
                    )
                )
            self.types.append(
                Type(
                    id=len(self.types),
                    kind=kind,
                    name=self._string(name_off),
                    size=size,
                    members=members,
                    params=params,
                )
            )
            pos = body + _TRAILING.get(kind, lambda _vlen: 0)(vlen)

    def _string(self, offset: int) -> str:
        if offset == 0 or offset >= len(self._strings):
            return ""
        end = self._strings.index(b"\0", offset)
        return self._strings[offset:end].decode("utf-8", "replace")

    def get(self, type_id: int) -> Type | None:
        """The type with this id, or `None` if the id is out of range."""
        if 0 <= type_id < len(self.types):
            return self.types[type_id]
        return None

    def name_of(self, type_id: int) -> str | None:
        """The name of a type id, or `None` for void and unnamed types."""
        ty = self.get(type_id)
        return ty.name or None if ty else None

    def struct_named(self, name: str) -> Type | None:
        """The struct with this tag."""
        return self._by_name.get((KIND_STRUCT, name))

    def skip_qualifiers(self, type_id: int) -> Type | None:
        """Resolves through `const`/`volatile`/`typedef`/tags to the real type."""
        seen = 0
        ty = self.get(type_id)
        # A malformed chain could cycle; the bound is generous but finite.
        while ty is not None and ty.kind in _TRANSPARENT and seen < 16:
            ty = self.get(ty.ref)
            seen += 1
        return ty

    def function_prototype(self, type_id: int) -> Type | None:
        """The `FUNC_PROTO` a member's type points at, if it is a function pointer."""
        ty = self.skip_qualifiers(type_id)
        if ty is None or ty.kind != KIND_PTR:
            return None
        target = self.skip_qualifiers(ty.ref)
        return target if target is not None and target.kind == KIND_FUNC_PROTO else None

    def _is_const(self, type_id: int) -> bool:
        """Whether the qualifier chain to a type passes through `const`."""
        seen = 0
        ty = self.get(type_id)
        while ty is not None and ty.kind in _TRANSPARENT and seen < 16:
            if ty.kind == KIND_CONST:
                return True
            ty = self.get(ty.ref)
            seen += 1
        return False

    def _typedef_name(self, type_id: int) -> str | None:
        """The outermost typedef spelling of a type, if it has one.

        A scalar argument is written the way the kernel source writes it (`u32`,
        not `unsigned int`), because that is the spelling the emitter's
        scalar-type allowlist matches against.
        """
        seen = 0
        ty = self.get(type_id)
        while ty is not None and ty.kind in _TRANSPARENT and seen < 16:
            if ty.kind == KIND_TYPEDEF and ty.name:
                return ty.name
            ty = self.get(ty.ref)
            seen += 1
        return None

    def type_name(self, type_id: int) -> str | None:
        """A C-ish spelling of a type, the way the descriptor JSONs record one.

        A pointer to a named struct comes back as `struct sock *`, a scalar as
        the name the kernel spells it with. Anything the scrapers do not model
        (a function pointer, an array, an anonymous struct) comes back `None` so
        the caller skips it rather than inventing a name.
        """
        ty = self.skip_qualifiers(type_id)
        if ty is None:
            return None
        if ty.kind == KIND_VOID:
            return "void"
        if ty.kind == KIND_PTR:
            target = self.skip_qualifiers(ty.ref)
            if target is None:
                return None
            # `const` on the pointee is part of the spelling the descriptors
            # record, and the emitter's `__ign` / scalar matching reads it.
            qualifier = "const " if self._is_const(ty.ref) else ""
            if target.kind == KIND_VOID:
                return f"{qualifier}void *"
            if target.kind in (KIND_STRUCT, KIND_UNION) and target.name:
                tag = "struct" if target.kind == KIND_STRUCT else "union"
                return f"{qualifier}{tag} {target.name} *"
            scalar = self._typedef_name(ty.ref) or target.name
            if target.kind in (KIND_INT, KIND_FLOAT) and scalar:
                return f"{qualifier}{scalar} *"
            return None
        if ty.kind in (KIND_INT, KIND_FLOAT, KIND_ENUM, KIND_ENUM64):
            return self._typedef_name(type_id) or ty.name or None
        return None
