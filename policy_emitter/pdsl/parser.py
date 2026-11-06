"""Parse `.pol` source into the AST.

The Lark grammar in `grammar.lark` is the single source of truth for the
syntax. `parse` returns a `PolicyFile`; `lark_parse` exposes the raw Lark
tree (with token positions) for the LSP server.
"""

from __future__ import annotations

from functools import lru_cache
from pathlib import Path

from lark import Lark, Transformer, v_args
from lark.exceptions import UnexpectedInput

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

_GRAMMAR = (Path(__file__).parent / "grammar.lark").read_text()


class ParseError(Exception):
    """A syntax error with 1-based line/column, suitable for CLI and LSP."""

    def __init__(self, message: str, line: int, column: int):
        super().__init__(message)
        self.message = message
        self.line = line
        self.column = column


@lru_cache(maxsize=1)
def _lark() -> Lark:
    return Lark(
        _GRAMMAR,
        parser="earley",
        start="start",
        propagate_positions=True,
    )


def _strip_static(tok) -> str:
    return str(tok)[1:-1]


@v_args(inline=True)
class _ToAst(Transformer):
    def start(self, *items):
        pf = PolicyFile()
        for item in items:
            if isinstance(item, GlobalPredicate):
                pf.predicates.append(item)
            elif isinstance(item, OpPolicy):
                pf.policies.append(item)
            else:  # ("prologue", [stmt, ...]) — concatenated
                tag, stmts = item
                existing = getattr(pf, tag) or []
                setattr(pf, tag, existing + stmts)
        return pf

    def predicate(self, name, *rest):
        *params, body = rest
        return GlobalPredicate(str(name), [str(p) for p in params], body)

    def prologue(self, *exprs):
        return ("prologue", list(exprs))

    def vars_block(self, *names):
        return ("vars", [str(n) for n in names])

    def pre_block(self, *exprs):
        return ("pre", list(exprs))

    def post_block(self, *items):
        # `items` is a mix of plain-statement Exprs and `Branch` blocks.
        return ("post", list(items))

    def branch(self, kw, *body):
        return Branch(str(kw) == "taken", list(body))

    # op() signature: each field method returns a (slot, value) tuple; the
    # opcode value is a raw int, operand slots carry an Imm/TypedField.
    def op_opcode(self, tok):
        return ("opcode", int(str(tok), 0))

    def op_src_imm(self, tok):
        return ("src", ImmField(int(str(tok), 0)))

    def op_src_reg(self, _tok):
        return ("src", TypedField("REG"))

    def op_dst_imm(self, tok):
        return ("dst", ImmField(int(str(tok), 0)))

    def op_dst_reg(self, _tok):
        return ("dst", TypedField("REG"))

    def op_off_typed(self, ty):
        return ("off", TypedField(str(ty)))

    def op_imm_imm(self, tok):
        return ("imm", ImmField(int(str(tok), 0)))

    def op_imm_typed(self, ty):
        return ("imm", TypedField(str(ty)))

    def op_policy(self, *children):
        op = OpPolicy()
        slots: dict[str, object] = {}
        for tag, value in children:
            if tag in ("opcode", "src", "dst", "off", "imm"):
                slots[tag] = value
            elif tag == "vars":
                op.exists = value
            elif tag == "pre":
                op.pre = value
            elif tag == "post":
                op.post = value
        op.signature = OpSignature(
            opcode=slots["opcode"],
            src=slots.get("src"),
            dst=slots.get("dst"),
            off=slots.get("off"),
            imm=slots.get("imm"),
        )
        return op

    # expressions
    def implication(self, lhs, rhs):
        return Implication(lhs, rhs)

    def or_(self, lhs, rhs):
        return Or(lhs, rhs)

    def and_(self, lhs, rhs):
        return And(lhs, rhs)

    # atoms
    def type_judgment(self, term, ty):
        return TypeJudgment(term, str(ty))

    def equality(self, lhs, rhs):
        return Equality(lhs, rhs)

    def comparison(self, lhs, op, rhs):
        return Comparison(lhs, str(op), rhs)

    def predicate_call(self, name, *args):
        return PredicateCall(str(name), list(args))

    def forall(self, var, lo, hi, body):
        return Forall(str(var), lo, hi, body)

    def not_(self, operand):
        return Not(operand)

    def prop(self, term):
        return Prop(term)

    def hole(self):
        return Hole()

    # terms
    def bool_lit(self, tok):
        return BoolLit(str(tok) == "true")

    def add(self, lhs, rhs):
        return Add(lhs, rhs)

    def sub(self, lhs, rhs):
        return Sub(lhs, rhs)

    def mul(self, lhs, rhs):
        return Mul(lhs, rhs)

    def div(self, lhs, rhs):
        return Div(lhs, rhs)

    def mod(self, lhs, rhs):
        return Mod(lhs, rhs)

    def shl(self, lhs, rhs):
        return Shl(lhs, rhs)

    def shr(self, lhs, rhs):
        return Shr(lhs, rhs)

    def band(self, lhs, rhs):
        return BAnd(lhs, rhs)

    def bxor(self, lhs, rhs):
        return BXor(lhs, rhs)

    def bor(self, lhs, rhs):
        return BOr(lhs, rhs)

    def neg(self, operand):
        return Neg(operand)

    def bnot(self, operand):
        return BNot(operand)

    def cast(self, ty, operand):
        return Cast(str(ty), operand)

    def field(self, base, name):
        return Field(base, str(name))

    def slice(self, base, lo, hi):
        return Slice(base, lo, hi)

    def index(self, base, idx):
        return Index(base, idx)

    def reg(self, tok):
        return Reg(int(str(tok)[1:]))

    def var(self, tok):
        return Var(str(tok))

    def int_lit(self, tok):
        return IntLit(int(str(tok), 0))

    def static_term(self, tok):
        return Static(_strip_static(tok))


def lark_parse(text: str):
    """Parse to the raw Lark tree (token positions intact). Raises ParseError."""
    try:
        return _lark().parse(text)
    except UnexpectedInput as exc:
        raise ParseError(str(exc), exc.line, exc.column) from exc


def parse(text: str) -> PolicyFile:
    """Parse `.pol` source into a `PolicyFile`. Raises ParseError."""
    return _ToAst().transform(lark_parse(text))


def ast_of(tree):
    """Transform a tree or subtree from `lark_parse` into its AST node(s).

    Used by the source-preserving formatter to rebuild a single expression from
    its parse subtree without reparsing the whole file."""
    return _ToAst().transform(tree)
