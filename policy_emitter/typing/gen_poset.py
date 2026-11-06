"""Render the type poset in types.yaml as Hasse diagrams (one SVG per kind).

Usage (from policy_emitter/):
    uv run python typing/gen_poset.py            # writes typing/poset_<kind>.svg
    uv run python typing/gen_poset.py --dot      # also keeps the .dot sources

Output style: textbook Hasse diagram — labels only (no boxes), undirected
lines, nodes banded by rank. Rank is the length of the longest sub-chain
ending at a node; nodes with no subtypes have rank 0.

The diagram is the *covering relation* (transitive reduction) of the partial
order, so only minimal edges are drawn: a declared edge `a <: c` is omitted
whenever the order already forces it through some `a <: b <: c`. The bounds of
each kind are implicit — a type marked `top: true` is a supertype of every
other type in its kind, and `bottom: true` a subtype of every other — so those
edges need not be (and should not be) listed in `edges:`.
"""

from __future__ import annotations

import subprocess
import sys
from collections import defaultdict
from pathlib import Path

import yaml

HERE = Path(__file__).parent

# A subtyping edge as a (sub, sup) pair: sub <: sup.
Edge = tuple[str, str]


def load(path: Path) -> dict:
    with path.open() as f:
        return yaml.safe_load(f)


def implicit_bound_edges(types: dict) -> set[Edge]:
    """Edges forced by the kind's declared bounds.

    `top: true`  => supertype of every other type (everything sits below it).
    """
    edges: set[Edge] = set()
    for name, t in types.items():
        if t.get("top"):
            edges.update((other, name) for other in types if other != name)
    return edges


def reachable_sups(edges: set[Edge]) -> dict[str, set[str]]:
    """For each node, the set of all strict supertypes (transitive closure)."""
    direct: dict[str, set[str]] = defaultdict(set)
    for sub, sup in edges:
        direct[sub].add(sup)

    memo: dict[str, set[str]] = {}

    def up(node: str) -> set[str]:
        if node in memo:
            return memo[node]
        memo[node] = set()  # guard against cycles in malformed input
        acc: set[str] = set()
        for sup in direct.get(node, ()):
            acc.add(sup)
            acc |= up(sup)
        memo[node] = acc
        return acc

    return {sub: up(sub) for sub in list(direct)}


def transitive_reduction(edges: set[Edge]) -> set[Edge]:
    """Keep only covering edges: drop `a <: c` if some `a <: b <: c` exists."""
    reach = reachable_sups(edges)
    direct: dict[str, set[str]] = defaultdict(set)
    for sub, sup in edges:
        direct[sub].add(sup)

    cover: set[Edge] = set()
    for sub, sup in edges:
        if sub == sup:
            continue
        # Redundant iff a different direct supertype of `sub` already reaches `sup`.
        if any(sup in reach.get(mid, ()) for mid in direct[sub] if mid != sup):
            continue
        cover.add((sub, sup))
    return cover


def compute_ranks(types: dict, edges: set[Edge]) -> dict[str, int]:
    """rank(node) = 1 + max(rank(sub)) over all edges sub <: node; default 0."""
    subs_of: dict[str, list[str]] = defaultdict(list)
    for sub, sup in edges:
        subs_of[sup].append(sub)
    ranks = {name: 0 for name in types}
    changed = True
    while changed:
        changed = False
        for name in types:
            if subs_of[name]:
                new = 1 + max(ranks[s] for s in subs_of[name])
                if new != ranks[name]:
                    ranks[name] = new
                    changed = True
    return ranks


def emit_dot(spec: dict, kind: str) -> str:
    """Emit DOT for the covering relation of a single kind's sub-poset."""
    types = {n: t for n, t in spec["types"].items() if t["kind"] == kind}
    declared = {
        (e["sub"], e["sup"])
        for e in spec.get("edges", [])
        if e["sub"] in types and e["sup"] in types
    }
    order = declared | implicit_bound_edges(types)
    cover = transitive_reduction(order)
    ranks = compute_ranks(types, cover)

    by_rank: dict[int, list[str]] = defaultdict(list)
    for name in types:
        by_rank[ranks[name]].append(name)

    out: list[str] = []
    out.append(f"graph TypePoset_{kind} {{")
    out.append('  graph [rankdir=BT, nodesep=0.5, ranksep=0.9, splines=line];')
    out.append('  node  [shape=plaintext, fontname="Helvetica", fontsize=12, margin=0.05];')
    out.append('  edge  [color="#333333"];')
    out.append("")
    for r in sorted(by_rank):
        quoted = "; ".join(f'"{n}"' for n in by_rank[r])
        out.append(f"  {{ rank=same; {quoted}; }}")
    out.append("")
    for sub, sup in sorted(cover):
        out.append(f'  "{sub}" -- "{sup}";')
    out.append("}")
    return "\n".join(out) + "\n"


def main(argv: list[str]) -> None:
    keep_dot = "--dot" in argv
    spec = load(HERE / "types.yaml")
    for kind in spec["kinds"]:
        dot = emit_dot(spec, kind)
        dot_path = HERE / f"poset_{kind}.dot"
        svg_path = HERE / f"poset_{kind}.svg"
        dot_path.write_text(dot)
        subprocess.run(["dot", "-Tsvg", str(dot_path), "-o", str(svg_path)], check=True)
        if not keep_dot:
            dot_path.unlink()
        print(f"wrote {svg_path.relative_to(HERE.parent)}", file=sys.stderr)


if __name__ == "__main__":
    main(sys.argv[1:])
