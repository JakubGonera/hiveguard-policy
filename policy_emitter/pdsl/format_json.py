"""Export the AST to JSON.

Every AST node becomes an object tagged with `kind` (its dataclass name);
lists and scalars pass through. This is the machine-readable contract for
downstream consumers.
"""

from __future__ import annotations

import dataclasses
import json

from .ast import PolicyFile


def to_jsonable(node):
    """Convert an AST node (or list/scalar) to JSON-serialisable data."""
    if dataclasses.is_dataclass(node) and not isinstance(node, type):
        result = {"kind": type(node).__name__}
        for f in dataclasses.fields(node):
            result[f.name] = to_jsonable(getattr(node, f.name))
        return result
    if isinstance(node, list):
        return [to_jsonable(x) for x in node]
    return node


def format_policy_file(pf: PolicyFile) -> str:
    """Render a PolicyFile as indented JSON."""
    return json.dumps(to_jsonable(pf), indent=2)
