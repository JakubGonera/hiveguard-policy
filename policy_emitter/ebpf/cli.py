"""Command-line entry point for eBPF policy generation.

    ebpf generate [--format pol|json] [--out FILE] [--data-dir DIR] [--width N]
    ebpf compile  FILE.pol [--out FILE]
    ebpf fmt      FILE.pol [--write] [--width N]

`generate` is eBPF-specific (it reads the kernel JSONs); `compile` and `fmt`
are generic operations over the `pdsl` DSL, exposed here for convenience.
`fmt` reflows long lines while preserving comments and layout (only comment-free
expressions are rewrapped); it reads the source text, not the parsed AST.

Run as: `uv run python -m ebpf.cli ...` from the policy_emitter directory.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from pdsl.format_json import format_policy_file as to_json
from pdsl.format_pol import DEFAULT_WIDTH, format_source
from pdsl.format_pol import format_policy_file as to_pol
from pdsl.parser import ParseError, parse

from .emitter import build_policy_file


def _emit(text: str, out: Path | None) -> None:
    if out is None:
        sys.stdout.write(text if text.endswith("\n") else text + "\n")
    else:
        out.write_text(text if text.endswith("\n") else text + "\n")
        print(f"wrote {out}", file=sys.stderr)


def _read_policy(path: Path):
    try:
        return parse(path.read_text())
    except ParseError as exc:
        print(f"{path}:{exc.line}:{exc.column}: {exc.message}", file=sys.stderr)
        raise SystemExit(1) from exc


def main(argv: list[str] | None = None) -> None:
    parser = argparse.ArgumentParser(
        prog="ebpf", description="eBPF policy generation toolkit"
    )
    sub = parser.add_subparsers(dest="cmd", required=True)

    gen = sub.add_parser("generate", help="emit policies from the kernel JSONs")
    gen.add_argument("--format", choices=["pol", "json"], default="pol")
    gen.add_argument("--out", type=Path, default=None)
    gen.add_argument("--data-dir", type=Path, default=None)
    gen.add_argument("--width", type=int, default=DEFAULT_WIDTH, help="wrap column")

    comp = sub.add_parser("compile", help="parse a .pol file and export JSON")
    comp.add_argument("file", type=Path)
    comp.add_argument("--out", type=Path, default=None)

    fmt = sub.add_parser("fmt", help="reflow a .pol file, wrapping long lines (keeps comments)")
    fmt.add_argument("file", type=Path)
    fmt.add_argument("--write", action="store_true", help="rewrite in place")
    fmt.add_argument("--width", type=int, default=DEFAULT_WIDTH, help="wrap column")

    args = parser.parse_args(argv)

    if args.cmd == "generate":
        pf = build_policy_file(args.data_dir)
        text = to_json(pf) if args.format == "json" else to_pol(pf, args.width)
        _emit(text, args.out)
    elif args.cmd == "compile":
        pf = _read_policy(args.file)
        _emit(to_json(pf), args.out)
    elif args.cmd == "fmt":
        try:
            text = format_source(args.file.read_text(), args.width)
        except ParseError as exc:
            print(f"{args.file}:{exc.line}:{exc.column}: {exc.message}", file=sys.stderr)
            raise SystemExit(1) from exc
        _emit(text, args.file if args.write else None)


if __name__ == "__main__":
    main()
