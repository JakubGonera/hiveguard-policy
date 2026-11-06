"""pdsl - a small, domain-agnostic policy DSL.

This package is the reusable DSL library: grammar, AST, parser, formatters,
and the LSP server. It knows nothing about eBPF. The eBPF-specific policy
generation lives in the sibling `ebpf` package.

Public API:
    parse(text)        -> PolicyFile      parse .pol source
    lark_parse(text)   -> lark.Tree       raw parse tree (token positions)
    format_pol(pf)     -> str             render canonical .pol text
    format_json(pf)    -> str             render JSON export
    ParseError                            raised by parse, carries line/column
"""

from .ast import PolicyFile
from .format_json import format_policy_file as format_json
from .format_pol import format_policy_file as format_pol
from .parser import ParseError, lark_parse, parse

__all__ = [
    "PolicyFile",
    "parse",
    "lark_parse",
    "format_pol",
    "format_json",
    "ParseError",
]
