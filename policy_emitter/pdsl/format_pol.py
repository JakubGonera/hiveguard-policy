"""Render the AST back to canonical `.pol` text, wrapping long lines.

Precedence-aware: parentheses are emitted only where needed to preserve the
parse, so `format -> parse -> format` is idempotent over the *semantic*
content. The one exception is `OpPolicy.comment`: it renders as `#` lines but
the parser drops comments, so a parsed-then-reformatted policy loses it. Such
comments are display-only metadata that the emitter regenerates each run.

Layout uses a small Wadler/Leijen "fits-or-break" document engine (the family
behind Prettier/Black). A line is broken at its *lowest-precedence* connective
first (`->`, then `||`, then `&&`), recursing inward only when an operand still
overflows. Associative chains are flattened to n-ary lists: short uniform
operands are packed several per line (fill); large operands go one per line
(stack). Operators lead the continuation line; tighter operators inside a
broken chain indent one level deeper, so the boolean structure stays visible.

Because the rendering is a pure function of `(AST, width)` and the parser
ignores whitespace, re-formatting wrapped text reproduces it exactly.
"""

from __future__ import annotations

from dataclasses import dataclass

from .ast import (
    Add,
    And,
    BAnd,
    BNot,
    BoolLit,
    BOr,
    Branch,
    BXor,
    Cast,
    Comparison,
    Div,
    Equality,
    Field,
    Forall,
    GlobalPredicate,
    Hole,
    ImmField,
    Implication,
    Index,
    IntLit,
    Mod,
    Mul,
    Neg,
    Not,
    OpPolicy,
    OpSignature,
    Or,
    PolicyFile,
    PredicateCall,
    Prop,
    Reg,
    Shl,
    Shr,
    Slice,
    Static,
    Sub,
    TypedField,
    TypeJudgment,
    Var,
)

# Default wrap column and indentation step. The minimum number of operands that
# must fit per line for a chain to be packed (fill); below it the chain stacks
# one operand per line, so we never settle for the cramped "two-per-line" case.
DEFAULT_WIDTH = 120
NEST = 2
MIN_FILL = 3

# Expression precedence: higher binds tighter.
_IMPLICATION, _OR, _AND, _ATOM = 1, 2, 3, 4

# Term precedence (C arithmetic), higher binds tighter. Mirrors the grammar's
# term ladder: bitor < bitxor < bitand < shift < add < mul < unary < postfix.
_T_BOR, _T_BXOR, _T_BAND, _T_SHIFT, _T_ADD, _T_MUL, _T_UNARY, _T_POSTFIX = (
    1, 2, 3, 4, 5, 6, 7, 8,
)


def _term_prec(node) -> tuple[int, str]:
    """Return `(precedence, rendered)` for a term node. All binary term
    operators are left-associative, so a binary node renders its left operand
    at its own precedence and its right operand one tighter."""
    match node:
        case Reg(n):
            return _T_POSTFIX, f"R{n}"
        case Var(name):
            return _T_POSTFIX, name
        case IntLit(value):
            return _T_POSTFIX, str(value)
        case BoolLit(value):
            return _T_POSTFIX, "true" if value else "false"
        case Static(src):
            return _T_POSTFIX, f"${src}$"
        case Field(base, field):
            return _T_POSTFIX, f"{_term(base, _T_POSTFIX)}.{field}"
        case Slice(base, lo, hi):
            return _T_POSTFIX, f"{_term(base, _T_POSTFIX)}[{_term(lo)}:{_term(hi)}]"
        case Index(base, idx):
            return _T_POSTFIX, f"{_term(base, _T_POSTFIX)}[{_term(idx)}]"
        case Neg(operand):
            return _T_UNARY, f"-{_term(operand, _T_UNARY)}"
        case BNot(operand):
            return _T_UNARY, f"~{_term(operand, _T_UNARY)}"
        case Cast(ty, operand):
            return _T_UNARY, f"({ty}){_term(operand, _T_UNARY)}"
        case Mul(lhs, rhs):
            return _T_MUL, f"{_term(lhs, _T_MUL)} * {_term(rhs, _T_MUL + 1)}"
        case Div(lhs, rhs):
            return _T_MUL, f"{_term(lhs, _T_MUL)} / {_term(rhs, _T_MUL + 1)}"
        case Mod(lhs, rhs):
            return _T_MUL, f"{_term(lhs, _T_MUL)} % {_term(rhs, _T_MUL + 1)}"
        case Add(lhs, rhs):
            return _T_ADD, f"{_term(lhs, _T_ADD)} + {_term(rhs, _T_ADD + 1)}"
        case Sub(lhs, rhs):
            return _T_ADD, f"{_term(lhs, _T_ADD)} - {_term(rhs, _T_ADD + 1)}"
        case Shl(lhs, rhs):
            return _T_SHIFT, f"{_term(lhs, _T_SHIFT)} << {_term(rhs, _T_SHIFT + 1)}"
        case Shr(lhs, rhs):
            return _T_SHIFT, f"{_term(lhs, _T_SHIFT)} >> {_term(rhs, _T_SHIFT + 1)}"
        case BAnd(lhs, rhs):
            return _T_BAND, f"{_term(lhs, _T_BAND)} & {_term(rhs, _T_BAND + 1)}"
        case BXor(lhs, rhs):
            return _T_BXOR, f"{_term(lhs, _T_BXOR)} ^ {_term(rhs, _T_BXOR + 1)}"
        case BOr(lhs, rhs):
            return _T_BOR, f"{_term(lhs, _T_BOR)} | {_term(rhs, _T_BOR + 1)}"
    raise TypeError(f"not a term: {node!r}")


def _term(node, min_prec: int = 0) -> str:
    """Render a term, parenthesising it only when its precedence is below the
    context's `min_prec` (so output reparses to the same tree, minimal parens).
    Terms are never line-wrapped: they model single-value ALU expressions and
    stay atomic on the line that carries them."""
    prec, rendered = _term_prec(node)
    return f"({rendered})" if prec < min_prec else rendered


def _relatom(node) -> str:
    """Render a non-breaking relational atom to a flat string."""
    match node:
        case TypeJudgment(term, ty):
            return f"{_term(term)} : {ty}"
        case Equality(lhs, rhs):
            return f"{_term(lhs)} = {_term(rhs)}"
        case Comparison(lhs, op, rhs):
            return f"{_term(lhs)} {op} {_term(rhs)}"
        case Prop(term):
            return _term(term)
        case Static():
            return _term(node)
        case Hole():
            return "..."
    raise TypeError(f"not a relational atom: {node!r}")


# --- Layout document engine (Wadler/Leijen "fits-or-break") ----------------
#
# A document is a tree of these nodes. `_render` lays it out within a width:
#   _Text       literal text, never split
#   _Line       a space when its group fits flat, else a newline + indent
#   _SoftBreak  nothing when flat, else a newline + indent (used to hug parens)
#   _Concat     a sequence
#   _Nest       deeper indentation for the breaks inside it
#   _Group      print flat if it fits the remaining width, else break
#   _Fill       pack chunks greedily, breaking only when the next won't fit


@dataclass(frozen=True)
class _Text:
    s: str


@dataclass(frozen=True)
class _Line:
    pass


@dataclass(frozen=True)
class _SoftBreak:
    pass


@dataclass(frozen=True)
class _Concat:
    parts: tuple


@dataclass(frozen=True)
class _Nest:
    n: int
    doc: object


@dataclass(frozen=True)
class _Group:
    doc: object


@dataclass(frozen=True)
class _Fill:
    chunks: tuple


LINE = _Line()
SOFT = _SoftBreak()

_FLAT, _BREAK = 0, 1


def _flat(d) -> str:
    """The fully-flattened (single-line) rendering of a document."""
    if isinstance(d, _Text):
        return d.s
    if isinstance(d, _Line):
        return " "
    if isinstance(d, _SoftBreak):
        return ""
    if isinstance(d, _Concat):
        return "".join(_flat(p) for p in d.parts)
    if isinstance(d, _Nest):
        return _flat(d.doc)
    if isinstance(d, _Group):
        return _flat(d.doc)
    if isinstance(d, _Fill):
        return " ".join(_flat(c) for c in d.chunks)
    raise TypeError(f"bad doc: {d!r}")


def _fits(w: int, stack: list, head: tuple) -> bool:
    """Does `head`, followed by the continuation in `stack`, fit flat in `w`
    columns before the next forced break? `stack` items keep their own mode, so
    a continuation that would break ends the line and counts as fitting."""
    work = [head]
    si = len(stack) - 1
    while w >= 0:
        if work:
            i, mode, d = work.pop()
        elif si >= 0:
            i, mode, d = stack[si]
            si -= 1
        else:
            return True
        if isinstance(d, _Text):
            w -= len(d.s)
        elif isinstance(d, _Line):
            if mode == _FLAT:
                w -= 1
            else:
                return True
        elif isinstance(d, _SoftBreak):
            if mode == _BREAK:
                return True
        elif isinstance(d, _Concat):
            for p in reversed(d.parts):
                work.append((i, mode, p))
        elif isinstance(d, _Nest):
            work.append((i + d.n, mode, d.doc))
        elif isinstance(d, _Group):
            work.append((i, _FLAT, d.doc))
        elif isinstance(d, _Fill):
            w -= len(_flat(d))
    return False


def _render(doc, width: int, indent0: int) -> str:
    """Lay out `doc` at column `indent0`, wrapping breaks that overflow `width`."""
    out = [" " * indent0]
    col = indent0
    stack = [(indent0, _BREAK, doc)]
    while stack:
        i, mode, d = stack.pop()
        if isinstance(d, _Text):
            out.append(d.s)
            col += len(d.s)
        elif isinstance(d, _Concat):
            for p in reversed(d.parts):
                stack.append((i, mode, p))
        elif isinstance(d, _Nest):
            stack.append((i + d.n, mode, d.doc))
        elif isinstance(d, _Line):
            if mode == _FLAT:
                out.append(" ")
                col += 1
            else:
                out.append("\n" + " " * i)
                col = i
        elif isinstance(d, _SoftBreak):
            if mode == _BREAK:
                out.append("\n" + " " * i)
                col = i
        elif isinstance(d, _Group):
            head = (i, _FLAT, d.doc)
            stack.append(head if _fits(width - col, stack, head) else (i, _BREAK, d.doc))
        elif isinstance(d, _Fill):
            first = _flat(d.chunks[0])
            out.append(first)
            col += len(first)
            for c in d.chunks[1:]:
                s = _flat(c)
                if col + 1 + len(s) <= width:
                    out.append(" " + s)
                    col += 1 + len(s)
                else:
                    out.append("\n" + " " * i + s)
                    col = i + len(s)
        else:
            raise TypeError(f"bad doc: {d!r}")
    return "".join(out)


# --- AST -> document -------------------------------------------------------


def _flatten_left(node, cls) -> list:
    """Flatten a left-associative chain `((a op b) op c)` to `[a, b, c]`."""
    out: list = []

    def go(n):
        if isinstance(n, cls):
            go(n.lhs)
            out.append(n.rhs)
        else:
            out.append(n)

    go(node)
    return out


def _flatten_right(node, cls) -> list:
    """Flatten a right-associative chain `(a op (b op c))` to `[a, b, c]`."""
    out: list = []

    def go(n):
        if isinstance(n, cls):
            out.append(n.lhs)
            go(n.rhs)
        else:
            out.append(n)

    go(node)
    return out


def _chain_info(node):
    """For a connective node, return `(prec, op, operands, operand_min_precs)`;
    `None` for any non-chain node. Operand min-precedences encode where parens
    are needed: left operands of `||`/`&&` and the last operand of `->` may sit
    one precedence looser than the rest."""
    if isinstance(node, Implication):
        ops = _flatten_right(node, Implication)
        precs = [_IMPLICATION + 1] * (len(ops) - 1) + [_IMPLICATION]
        return _IMPLICATION, "->", ops, precs
    if isinstance(node, Or):
        ops = _flatten_left(node, Or)
        return _OR, "||", ops, [_OR] + [_OR + 1] * (len(ops) - 1)
    if isinstance(node, And):
        ops = _flatten_left(node, And)
        return _AND, "&&", ops, [_AND] + [_AND + 1] * (len(ops) - 1)
    return None


def _build_chain(op: str, op_docs: list, indent: int, width: int):
    """Assemble a flattened chain. Small uniform operands fill (several per
    line); otherwise each operand stacks on its own line with a leading op."""
    flat_widths = [len(_flat(d)) for d in op_docs]
    avail = max(width - indent, 1)
    unit = max(flat_widths) + len(op) + 2
    if avail // unit >= MIN_FILL and max(flat_widths) <= avail:
        chunks = [op_docs[0]] + [_Concat((_Text(op + " "), d)) for d in op_docs[1:]]
        return _Fill(tuple(chunks))
    parts: list = [op_docs[0]]
    for d in op_docs[1:]:
        parts += [LINE, _Text(op + " "), d]
    return _Group(_Concat(tuple(parts)))


def _wrap_parens(doc, indent: int):
    """Parenthesise a chain; when it spans lines, `(` and `)` get their own
    lines and the body indents one level (the `)` dedents back to `indent`)."""
    return _Group(_Concat((
        _Text("("),
        _Nest(NEST, _Concat((SOFT, doc))),
        SOFT,
        _Text(")"),
    )))


def _expr_doc(node, min_prec: int, indent: int, width: int):
    """Build a layout document for an expression. `indent` is the column its
    continuation lines (and any nested operands) are measured/rendered at."""
    info = _chain_info(node)
    if info is None:
        return _atom_doc(node, indent, width)
    prec, op, operands, precs = info
    parens = prec < min_prec
    chain_indent = indent + NEST if parens else indent
    op_docs = []
    for child, cp in zip(operands, precs):
        cinfo = _chain_info(child)
        if cinfo is not None and cinfo[0] < cp:
            # Child is parenthesised; it provides its own inner indentation.
            op_docs.append(_expr_doc(child, cp, chain_indent, width))
        elif cinfo is not None:
            # Tighter sub-chain: nest it so its breaks sit one level deeper.
            op_docs.append(_Nest(NEST, _expr_doc(child, cp, chain_indent + NEST, width)))
        else:
            op_docs.append(_atom_doc(child, chain_indent, width))
    doc = _build_chain(op, op_docs, chain_indent, width)
    return _wrap_parens(doc, indent) if parens else doc


def _predcall_doc(node: PredicateCall, indent: int, width: int):
    if not node.args:
        return _Text(f"{node.name}()")
    inner = _Text(_term(node.args[0]))
    for a in node.args[1:]:
        inner = _Concat((inner, _Text(","), LINE, _Text(_term(a))))
    return _Group(_Concat((
        _Text(node.name + "("),
        _Nest(NEST, _Concat((SOFT, inner))),
        SOFT,
        _Text(")"),
    )))


def _atom_doc(node, indent: int, width: int):
    if isinstance(node, (TypeJudgment, Equality, Comparison, Prop, Static, Hole)):
        return _Text(_relatom(node))
    if isinstance(node, PredicateCall):
        return _predcall_doc(node, indent, width)
    if isinstance(node, Forall):
        body = _expr_doc(node.body, 0, indent + NEST, width)
        return _Group(_Concat((
            _Text(f"for ({node.var} in {_term(node.lo)}:{_term(node.hi)}) {{"),
            _Nest(NEST, _Concat((LINE, body))),
            LINE,
            _Text("}"),
        )))
    if isinstance(node, Not):
        inner = _expr_doc(node.operand, _ATOM, indent, width)
        # Self-delimiting atoms (calls, holes, nested !) need no parens;
        # relational atoms get them so `!` is not misread as binding the left
        # term alone. Chains are already parenthesised by `_expr_doc`.
        if isinstance(node.operand, (TypeJudgment, Equality, Comparison, Prop)):
            inner = _Concat((_Text("("), inner, _Text(")")))
        return _Concat((_Text("!"), inner))
    raise TypeError(f"not an atom: {node!r}")


def format_expr(node, width: int = DEFAULT_WIDTH, indent: int = 0) -> str:
    """Format a single expression with minimal parentheses, wrapped to `width`."""
    return _render(_expr_doc(node, 0, indent, width), width, indent)


# --- top-level declarations ------------------------------------------------


def _stmt(e, indent: int, width: int) -> str:
    """A `;`-terminated statement, its first line indented to `indent`."""
    return _render(_Concat((_expr_doc(e, 0, indent, width), _Text(";"))), width, indent)


def _predicate(pred: GlobalPredicate, width: int) -> str:
    header = f"{pred.name}({', '.join(pred.params)}) :="
    doc = _Group(_Concat((
        _Text(header),
        _Nest(NEST, _Concat((LINE, _expr_doc(pred.body, 0, NEST, width)))),
        _Text(";"),
    )))
    return _render(doc, width, 0)


def _imm(value: int) -> str:
    """Render an op-signature immediate as hex (instruction-field encoding)."""
    return f"-0x{-value:x}" if value < 0 else f"0x{value:x}"


def _op_field(slot: str, fld) -> str:
    match fld:
        case ImmField(value):
            return f"{slot} = {_imm(value)}"
        case TypedField(ty):
            return f"{slot} : {ty}"
    raise TypeError(f"not an op field: {fld!r}")


def _signature(sig: OpSignature) -> str:
    # Canonical order: opcode, src, dst, off, imm; absent slots are omitted.
    parts = [f"opcode = {_imm(sig.opcode)}"]
    for slot in ("src", "dst", "off", "imm"):
        fld = getattr(sig, slot)
        if fld is not None:
            parts.append(_op_field(slot, fld))
    return ", ".join(parts)


def _branch_block(branch: Branch, width: int) -> str:
    """Render a `taken { ... }` / `!taken { ... }` block at postcondition depth."""
    keyword = "taken" if branch.taken else "!taken"
    lines = [f"    {keyword} {{"]
    lines += [_stmt(e, 6, width) for e in branch.body]
    lines.append("    }")
    return "\n".join(lines)


def _op_policy(policy: OpPolicy, width: int) -> str:
    lines = [f"# {ln}" for ln in (policy.comment or "").splitlines()]
    lines.append(f"op({_signature(policy.signature)}) {{")
    if policy.exists:
        lines.append(f"  vars := {{{', '.join(policy.exists)}}}")
    lines.append("  preconditions {")
    lines += [_stmt(e, 4, width) for e in policy.pre]
    lines.append("  }")
    lines.append("  postconditions {")
    for item in policy.post:
        lines.append(
            _branch_block(item, width) if isinstance(item, Branch) else _stmt(item, 4, width)
        )
    lines.append("  }")
    lines.append("}")
    return "\n".join(lines)


def _stmt_block(keyword: str, stmts: list, width: int) -> str:
    lines = [f"{keyword} {{"]
    lines += [_stmt(e, 2, width) for e in stmts]
    lines.append("}")
    return "\n".join(lines)


def format_policy_file(pf: PolicyFile, width: int = DEFAULT_WIDTH) -> str:
    """Render a whole PolicyFile to canonical `.pol` text, wrapped to `width`.

    This is the AST-only path (used by the emitter); it does not carry source
    comments. To format existing `.pol` *text* while keeping its comments, use
    `format_source`."""
    blocks: list[str] = [_predicate(p, width) for p in pf.predicates]
    # The prologue sits between the predicates and the per-op policies
    # (matching the hand-written builtins.pol layout).
    if pf.prologue is not None:
        blocks.append(_stmt_block("prologue", pf.prologue, width))
    blocks += [_op_policy(p, width) for p in pf.policies]
    return "\n\n".join(blocks) + "\n"


# --- Source-preserving formatting (keeps comments) -------------------------
#
# The grammar `%ignore`s comments, so a parse -> AST -> text round trip drops
# them. A comment between two sub-expressions is anchored to a line break that
# reflowing would move, so it cannot be relocated safely. The formatter
# therefore rewrites only statement expressions that contain no interior
# comment, editing them in place; every comment, header, blank line, and piece
# of punctuation outside those expressions is left byte-for-byte. Trailing and
# standalone comments sit outside expression spans and survive automatically.


def _scan_comments(src: str) -> list[tuple[int, int]]:
    """`[start, end)` char spans of every `#` comment, skipping `$...$` escapes
    (the only construct whose text may contain a non-comment `#`)."""
    spans: list[tuple[int, int]] = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        if c == "$":
            j = src.find("$", i + 1)
            i = n if j == -1 else j + 1
        elif c == "#":
            j = src.find("\n", i)
            j = n if j == -1 else j
            spans.append((i, j))
            i = j
        else:
            i += 1
    return spans


def _overlaps(spans: list[tuple[int, int]], lo: int, hi: int) -> bool:
    return any(cs < hi and ce > lo for cs, ce in spans)


def _own_line(src: str, pos: int) -> bool:
    """True if `pos` is preceded only by whitespace on its line (so the
    construct starting there owns the line and can be safely rewrapped). Compact
    forms that pack several statements on one line are left untouched."""
    return not src[src.rfind("\n", 0, pos) + 1 : pos].strip()


def format_source(source: str, width: int = DEFAULT_WIDTH) -> str:
    """Reflow `.pol` *source* to `width`, preserving comments and layout.

    Only comment-free statement expressions (predicate bodies and the
    statements inside pre/post/prologue blocks) are rewrapped; anything
    with an interior comment is left exactly as written. Raises ParseError on
    invalid input."""
    from lark import Tree

    from .parser import ast_of, lark_parse

    tree = lark_parse(source)
    comments = _scan_comments(source)
    edits: list[tuple[int, int, str]] = []

    for t in tree.iter_subtrees():
        if t.data == "predicate":
            body = t.children[-1]
            if not isinstance(body, Tree) or body.meta.empty:
                continue
            e = body.meta.end_pos
            head = t.meta.start_pos
            col = head - (source.rfind("\n", 0, head) + 1)
            # `head..e` spans `name(params) := <body>`; the `:=` and header are
            # kept verbatim, the body is rebuilt and may break onto its own line
            # (header-aware, exactly like the AST path's enclosing group).
            if _overlaps(comments, head, e) or not _own_line(source, head):
                continue
            ws = body.meta.start_pos
            while ws > head and source[ws - 1] in " \t\r\n":
                ws -= 1
            # A phantom `;` keeps the trailing `;` (left in the source) inside
            # the fit calculation; it is stripped back off before splicing in.
            doc = _Group(_Concat((
                _Text(source[head:ws]),
                _Nest(NEST, _Concat((LINE, _expr_doc(ast_of(body), 0, col + NEST, width)))),
                _Text(";"),
            )))
            edits.append((head, e, _render(doc, width, col)[col:-1]))
        elif t.data in ("pre_block", "post_block", "prologue", "branch"):
            for c in t.children:
                if not isinstance(c, Tree) or c.meta.empty:
                    continue
                if c.data == "branch":
                    continue  # a nested taken/!taken block; reflowed on its own visit
                s, e = c.meta.start_pos, c.meta.end_pos
                if _overlaps(comments, s, e) or not _own_line(source, s):
                    continue
                col = s - (source.rfind("\n", 0, s) + 1)
                doc = _Concat((_expr_doc(ast_of(c), 0, col, width), _Text(";")))
                edits.append((s, e, _render(doc, width, col)[col:-1]))

    out = source
    for s, e, repl in sorted(edits, reverse=True):
        out = out[:s] + repl + out[e:]
    return out
