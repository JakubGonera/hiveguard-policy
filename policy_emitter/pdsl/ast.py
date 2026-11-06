"""Typed AST for the policy DSL.

Every node is a dataclass. Sum types are expressed as a union of dataclasses;
`format_json` tags each with its class name as `kind`. `format_pol` renders
them back to `.pol` text. The parser in `parser.py` is the only producer of
these nodes from source; the emitter constructs them directly.
"""

from __future__ import annotations

from dataclasses import dataclass, field

# --- Terms -----------------------------------------------------------------


@dataclass
class Reg:
    """An eBPF register, R0..R10."""

    n: int


@dataclass
class Var:
    """A bound/free variable, op-arg, or named constant (e.g. STACK_SIZE)."""

    name: str


@dataclass
class IntLit:
    value: int


@dataclass
class BoolLit:
    value: bool


@dataclass
class Static:
    """A `$...$` escape: a helper computation over static inputs."""

    src: str


@dataclass
class Field:
    """Field access, `base.field`."""

    base: "Term"
    field: str


@dataclass
class Slice:
    """A memory slice, `base[lo:hi]` (e.g. STACK[off:off+size]).

    `base` is a postfix term, so a field can be sliced: `slot.bytes[lo:hi]`.
    """

    base: "Term"
    lo: "Term"
    hi: "Term"


@dataclass
class Index:
    """A single-element index, `base[idx]` (e.g. STACK[i]).

    `base` is a postfix term, so a field can be indexed: `slot.init[b]`.
    """

    base: "Term"
    index: "Term"


@dataclass
class Add:
    lhs: "Term"
    rhs: "Term"


@dataclass
class Sub:
    lhs: "Term"
    rhs: "Term"


@dataclass
class Mul:
    lhs: "Term"
    rhs: "Term"


@dataclass
class Div:
    """Division, `lhs / rhs` (unsigned unless operands are signed-cast)."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class Mod:
    """Modulo, `lhs % rhs`. Multiplicative precedence, like `*`/`/` (C)."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class Shl:
    """Left shift, `lhs << rhs`."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class Shr:
    """Right shift, `lhs >> rhs` (logical; arithmetic via a signed-cast lhs)."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class BAnd:
    """Bitwise and, `lhs & rhs` (distinct from the logical `&&`)."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class BXor:
    """Bitwise xor, `lhs ^ rhs`."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class BOr:
    """Bitwise or, `lhs | rhs` (distinct from the logical `||`)."""

    lhs: "Term"
    rhs: "Term"


@dataclass
class Neg:
    """Unary arithmetic negation, `-operand` (eBPF BPF_NEG)."""

    operand: "Term"


@dataclass
class BNot:
    """Unary bitwise complement, `~operand`."""

    operand: "Term"


@dataclass
class Cast:
    """A C-style width cast, `(type)operand`.

    `type` is a width keyword `u8/u16/u32/u64/s8/s16/s32/s64`. Models the
    truncation + zero/sign-extension that eBPF ALU width and `BPF_END` apply:
    `(u32)x` keeps the low 32 bits and zero-extends; `(s64)x` sign-extends.
    """

    type: str
    operand: "Term"


Term = (
    Reg
    | Var
    | IntLit
    | BoolLit
    | Static
    | Field
    | Slice
    | Index
    | Add
    | Sub
    | Mul
    | Div
    | Mod
    | Shl
    | Shr
    | BAnd
    | BXor
    | BOr
    | Neg
    | BNot
    | Cast
)

# --- Atoms (relational leaves) and expressions -----------------------------


@dataclass
class TypeJudgment:
    """`term : TYPE`."""

    term: Term
    type: str


@dataclass
class Equality:
    """`lhs = rhs`."""

    lhs: Term
    rhs: Term


@dataclass
class Comparison:
    """`lhs op rhs` for op in >= <= > < !=."""

    lhs: Term
    op: str
    rhs: Term


@dataclass
class PredicateCall:
    """`name(arg, ...)`."""

    name: str
    args: list[Term]


@dataclass
class Prop:
    """A bare term asserted as a proposition (e.g. a boolean variable)."""

    term: Term


@dataclass
class Forall:
    """Bounded universal quantifier: `body` holds for every `var` in `lo:hi`.

    The upper bound is exclusive, mirroring the kernel's `for (i = lo;
    i < hi; i++)` verifier loops (e.g. the stack-slot scan).
    """

    var: str
    lo: Term
    hi: Term
    body: "Expr"


@dataclass
class Not:
    """Logical negation, `!operand`. Binds tighter than `&&`/`||`/`->`."""

    operand: "Expr"


@dataclass
class Hole:
    """The `...` placeholder for an unfinished policy fragment."""


@dataclass
class And:
    lhs: "Expr"
    rhs: "Expr"


@dataclass
class Or:
    lhs: "Expr"
    rhs: "Expr"


@dataclass
class Implication:
    lhs: "Expr"
    rhs: "Expr"


Atom = (
    TypeJudgment
    | Equality
    | Comparison
    | PredicateCall
    | Forall
    | Prop
    | Hole
    # A bare `$...$` escape (Static) is itself a valid atom — useful for the
    # emitter to drop in raw side-condition fragments without wrapping in Prop.
    | Static
)
# `Not` lives at the Expr level alongside the binary connectives: it's a
# logical operator, not a leaf. The grammar still binds `!` tighter than
# `&&`/`||`/`->`, but at the AST level any Expr can be negated.
Expr = Atom | And | Or | Implication | Not

# --- Top-level declarations ------------------------------------------------


@dataclass
class GlobalPredicate:
    """A named predicate definition, `name(params) := body;`."""

    name: str
    params: list[str]
    body: Expr


# --- Op-policy instruction signature ---------------------------------------


@dataclass
class ImmField:
    """An instruction field constrained to a concrete immediate: `field = N`."""

    value: int


@dataclass
class TypedField:
    """A symbolic instruction operand bound by type: `field : TYPE`.

    `src`/`dst` carry `REG`; `off` carries `S16` (signed); `imm` carries
    `U64`/`U32`. The field name (src, dst, off, imm) is bound as a variable
    usable in the pre-/postcondition body.
    """

    type: str


# A signature slot is either an immediate match or a symbolic typed operand.
OpField = ImmField | TypedField


@dataclass
class OpSignature:
    """The decoded-instruction signature of an `op(...)` policy.

    `opcode` is always a concrete immediate (the instruction selector). The
    operand slots are optional; each, when present, is an `ImmField` (`= N`) or
    a `TypedField` (`: REG` for src/dst, `: S16` for off, `: U64`/`: U32` for
    imm).
    """

    opcode: int
    src: OpField | None = None
    dst: OpField | None = None
    off: OpField | None = None
    imm: OpField | None = None


@dataclass
class Branch:
    """A successor-conditioned postcondition block of a conditional jump.

    `taken=True` renders as `taken { ... }` and carries the facts that hold on
    the branch-taken edge (PC += off); `taken=False` renders as `!taken { ... }`
    and carries the facts on the fall-through edge. The body is a statement list
    exactly like a postcondition body. Only valid inside `postconditions`.
    """

    taken: bool
    body: list["Expr"] = field(default_factory=list)


# A postcondition item is a plain statement (holds on both successors) or a
# successor-conditioned `Branch` block.
PostItem = Expr | Branch


@dataclass
class OpPolicy:
    """A per-operation/helper policy block: a Hoare triple `op(...) { ... }`.

    `signature` carries the decoded-instruction shape. `comment` is an optional
    human-readable note rendered as `#` lines above the policy (the emitter
    uses it to record which helper proto a `BPF_CALL` imm denotes, since many
    protos share one func id); it is for display only and is not recovered by
    the parser.

    `post` may contain `Branch` blocks (only meaningful for conditional jumps);
    `pre` is always a flat statement list.
    """

    signature: OpSignature | None = None
    comment: str | None = None
    exists: list[str] = field(default_factory=list)
    pre: list[Expr] = field(default_factory=list)
    post: list[PostItem] = field(default_factory=list)

    @staticmethod
    def merge_guarded(variants: list[tuple["OpPolicy", Expr]]) -> "OpPolicy":
        """Merge op-policies sharing a signature into one guarded triple.

        `variants` is a non-empty list of `(policy, guard)` pairs; `guard` is the
        condition selecting that variant (e.g. its access-check call). The result
        keeps statements common to *every* variant once, gates each variant's
        remaining statements under `guard -> ...`, and (preconditions only)
        asserts the disjunction of all guards, so the operation is permitted only
        in a context that selects some variant. Variant bodies must be flat
        statement lists (no `Branch`), as helper-call triples are.

        Sound because the guard disjunction forces at least one variant active
        and the guards are mutually exclusive per call site: a statement required
        or granted by all variants holds unconditionally, while a variant-unique
        statement is required/granted exactly when that variant is selected.
        """
        policies = [p for p, _ in variants]
        guards = [g for _, g in variants]
        base = policies[0]

        def conjoin(atoms: list[Expr]) -> Expr:
            acc = atoms[0]
            for a in atoms[1:]:
                acc = And(acc, a)
            return acc

        def section(seqs: list[list[Expr]]) -> tuple[list[Expr], list[Expr]]:
            shared = [s for s in seqs[0] if all(s in other for other in seqs[1:])]
            guarded: list[Expr] = []
            for guard, seq in zip(guards, seqs):
                extra = [s for s in seq if s not in shared]
                if extra:
                    guarded.append(Implication(guard, conjoin(extra)))
            return shared, guarded

        pre_shared, pre_guarded = section([p.pre for p in policies])
        post_shared, post_guarded = section([p.post for p in policies])

        guard_disjunction = guards[0]
        for g in guards[1:]:
            guard_disjunction = Or(guard_disjunction, g)

        exists: list[str] = []
        comments: list[str] = []
        for p in policies:
            for v in p.exists:
                if v not in exists:
                    exists.append(v)
            if p.comment and p.comment not in comments:
                comments.append(p.comment)

        return OpPolicy(
            signature=base.signature,
            comment="\n".join(comments) or None,
            exists=exists,
            pre=[*pre_shared, *pre_guarded, guard_disjunction],
            post=[*post_shared, *post_guarded],
        )


@dataclass
class PolicyFile:
    """A whole `.pol` file.

    Layout: predicate definitions, an optional `prologue` statement block, and
    the per-op policies. The prologue is a flat list of statements (each an
    `Expr`, exactly like a pre-/post-condition body) emitted before the policy
    set.
    """

    predicates: list[GlobalPredicate] = field(default_factory=list)
    # `None` means the block is absent; `[]` means a present-but-empty block
    # (so the canonical formatter round-trips an empty `prologue {}`).
    prologue: list[Expr] | None = None
    policies: list[OpPolicy] = field(default_factory=list)
