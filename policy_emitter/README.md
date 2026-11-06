# policy_emitter

A pipeline that derives eBPF verifier-equivalent preconditions and
postconditions for helper-function calls, grounded in type information taken
directly from the running kernel.

## Running

Regenerate the three input JSONs (web scrape + drgn dump + kprobe capture).
Steps 2–4 prompt for sudo as needed:

```
./build_jsons.sh
```

Then emit policies (run from this directory):

```
uv run python -m ebpf.cli generate --format pol   # canonical .pol text
uv run python -m ebpf.cli generate --format json  # machine-readable AST
```

`generate` reads the three input JSONs and emits one policy block per helper
whose argument/return types it knows how to translate.

The legacy `policy_emitter.py` script prints the same policies as plain text
with no parser; it is superseded by the packages below and kept only for
reference.

## Layout: `pdsl` (DSL library) and `ebpf` (specific logic)

The code is split between the reusable, domain-agnostic DSL library and the
eBPF-specific policy logic.

`pdsl/` - the policy DSL library (knows nothing about eBPF):

| File | Role |
|---|---|
| `pdsl/grammar.lark` | Grammar - the single source of truth for `.pol` syntax. |
| `pdsl/ast.py` | Typed AST (dataclasses) for terms, atoms, predicates, policies. |
| `pdsl/parser.py` | `.pol` text -> AST (Lark); parse errors carry line/column. |
| `pdsl/format_pol.py` | AST -> canonical `.pol` text. |
| `pdsl/format_json.py` | AST -> JSON (every node tagged with `kind`). |
| `pdsl/__init__.py` | Public API: `parse`, `format_pol`, `format_json`, ... |
| `pdsl/lsp/` | LSP server: parse diagnostics + semantic tokens. |
| `pdsl/vscode/` | VSCode extension (see `pdsl/vscode/README.md`). |

`ebpf/` - the eBPF-specific policy generation:

| File | Role |
|---|---|
| `ebpf/emitter.py` | Kernel JSONs -> AST (the ported generation logic). |
| `ebpf/builtins.pol` | Hand-written predicates and op policies (`scratch`, `MAP_BY_FD`, ...) merged into every emitted file. |
| `ebpf/cli.py` | `generate`, `compile FILE.pol`, `fmt FILE.pol`. |

CLI:

```
uv run python -m ebpf.cli generate [--format pol|json] [--out FILE]
uv run python -m ebpf.cli compile FILE.pol [--out FILE]   # parse -> JSON
uv run python -m ebpf.cli fmt FILE.pol [--write]          # canonical re-print
```

## Input JSONs

| File | Producer | Source | Contents |
|---|---|---|---|
| `docs_helper_callers.json` | `prog_helpers_scraper.py` | web scrape of [isovalent/ebpf-docs](https://github.com/isovalent/ebpf-docs)' `helpers-functions.yaml` | For each helper name, the program types the public docs say are allowed to call it. Static, documentation-derived. |
| `kernel_proto_descriptors.json` | `helper_proto_scraper.py` (drgn) | `bpf_func_proto` objects in the **vendored** `vmlinux` | Per-proto record: name, `func_id`, return type, arg types, `gpl_only`, `pkt_access`. A proto is `const` initialised data, so it reads straight out of the built image. |
| `probed_proto_callers.json` | `dispatch_probe/cleanup_results.py` | kprobe capture (see `dispatch_probe/`) + drgn enum lookup | For each `bpf_func_proto` symbol: helper id, helper function name (`bpf_xxx`), and the program types whose verifier dispatch actually resolves to this proto. The one genuinely dynamic input: it observes dispatch, which no static image records, so it must run **inside the VM** against the vendored kernel. |
| `kfunc_descriptors.json` | `kfunc_descriptor_scraper.py` | vendored kernel source + the built image's `.BTF` | Per-kfunc record: KF_* flags, the hooks it is registered under, its filter, and its signature. The BTF id is a snapshot of this build: the kernel assigns ids at load, so nothing may key on it. |
| `struct_ops_descriptors.json` | `struct_ops_scraper.py` | vendored kernel source + the built image's `.BTF` | Per struct_ops type, each function-pointer member's name, byte offset and prototype. What lets a struct_ops program's trampoline context slots be typed. |

The scapers read `.vm/linux-build/<arch>/vmlinux`, so `just linux-build` must have run first;
pass `--vmlinux` to point elsewhere. The image's `PT_LOAD` segments serve as
drgn's memory (`scrapers/vmlinux.py`) and its `.BTF` section supplies type names
(`scrapers/btf.py`), so none of them need root or a live kernel. Each output
carries a `provenance` stamp naming the kernel release and build id it came
from, and `emitter.py` refuses to build a policy from files that disagree.

The docs give the specification for access requirements to helper calls (program types, but also attach types, capabilities and kconfigs), whereas the probed protos link the specific function proto to an abstract id (concrete definition of a helper depends on the calling type).