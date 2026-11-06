"""A small LSP server for `.pol` files.

Three features, all backed by the same grammar/parser/formatter as the emitter:
  * diagnostics  - parse errors reported at their line/column
  * semantic tokens - identifiers classified (type / variable / function / ...)
    by their position in the parse tree, which a TextMate grammar cannot do.
  * formatting   - canonical re-print with long lines wrapped (VSCode "Format
    Document"). Wrap column = $PDSL_FORMAT_WIDTH (default 120).

Run as: `python -m pdsl.lsp.server` (stdio transport).
"""

from __future__ import annotations

import os

from lark import Token, Tree
from lsprotocol import types
from pygls.lsp.server import LanguageServer

from ..format_pol import DEFAULT_WIDTH, format_source
from ..parser import ParseError, lark_parse

_FORMAT_WIDTH = int(os.environ.get("PDSL_FORMAT_WIDTH") or DEFAULT_WIDTH)

TOKEN_TYPES = [
    "keyword",
    "variable",
    "type",
    "enumMember",
    "function",
    "parameter",
    "number",
    "string",
    "operator",
    "property",
]

server = LanguageServer("pdsl-language-server", "v0.1")


# --- semantic-token classification ----------------------------------------


def _classify(tree: Tree) -> list[tuple[int, int, int, str]]:
    """Collect (line, column, length, token-type) for every token in `tree`."""
    out: list[tuple[int, int, int, str]] = []

    def emit(tok: Token, ttype: str) -> None:
        out.append((tok.line, tok.column, len(tok.value), ttype))

    def recur(node) -> None:
        if isinstance(node, Tree):
            out.extend(_classify(node))

    data = tree.data
    children = tree.children

    if data == "predicate":
        emit(children[0], "function")
        for c in children[1:-1]:
            emit(c, "parameter")
        recur(children[-1])
    elif data == "op_policy":
        # `op`, the field-name keywords (opcode/src/dst/imm) and the `:`/`=`
        # punctuation are anonymous literals (filtered out); recurse into the
        # signature-field subtrees and the vars/pre/post blocks.
        for c in children:
            recur(c)
    elif data in ("op_opcode", "op_src_imm", "op_dst_imm", "op_imm_imm"):
        emit(children[0], "number")  # the immediate value
    elif data in ("op_src_reg", "op_dst_reg", "op_off_typed", "op_imm_typed"):
        emit(children[0], "type")  # REG / U16 / U64 / U32 operand type
    elif data == "vars_block":
        for c in children:
            emit(c, "parameter")
    elif data == "branch":
        emit(children[0], "keyword")  # the `taken` / `!taken` selector
        for c in children[1:]:
            recur(c)
    elif data == "type_judgment":
        recur(children[0])
        emit(children[1], "type")
    elif data == "predicate_call":
        emit(children[0], "function")
        for c in children[1:]:
            recur(c)
    elif data == "cast":
        emit(children[0], "type")  # the (u32)/(s64) width keyword
        recur(children[1])
    elif data == "field":
        recur(children[0])
        emit(children[1], "property")
    elif data == "slice":
        recur(children[0])  # base is a postfix term (e.g. STACK or slot.bytes)
        recur(children[1])
        recur(children[2])
    elif data == "index":
        recur(children[0])  # base is a postfix term (e.g. STACK or slot.init)
        recur(children[1])
    elif data == "forall":
        emit(children[0], "parameter")  # the bound loop variable
        for c in children[1:]:
            recur(c)
    elif data == "reg":
        emit(children[0], "variable")
    elif data == "var":
        emit(children[0], "variable")
    elif data == "int_lit":
        emit(children[0], "number")
    elif data == "static_term":
        emit(children[0], "string")
    elif data == "bool_lit":
        emit(children[0], "keyword")
    else:  # start, prologue, pre/post_block, and_/or_/implication, equality, comparison, prop
        for c in children:
            if isinstance(c, Tree):
                recur(c)
            elif isinstance(c, Token) and c.type == "CMP":
                emit(c, "operator")
    return out


def _encode(tokens: list[tuple[int, int, int, str]]) -> list[int]:
    """Delta-encode classified tokens into the LSP semantic-tokens array."""
    data: list[int] = []
    prev_line = prev_col = 0
    for line, column, length, ttype in sorted(tokens):
        line0, col0 = line - 1, column - 1
        delta_line = line0 - prev_line
        delta_col = col0 - prev_col if delta_line == 0 else col0
        data += [delta_line, delta_col, length, TOKEN_TYPES.index(ttype), 0]
        prev_line, prev_col = line0, col0
    return data


# --- features --------------------------------------------------------------


def _validate(ls: LanguageServer, uri: str) -> None:
    doc = ls.workspace.get_text_document(uri)
    diagnostics: list[types.Diagnostic] = []
    try:
        lark_parse(doc.source)
    except ParseError as exc:
        line = max(exc.line - 1, 0)
        col = max(exc.column - 1, 0)
        diagnostics.append(
            types.Diagnostic(
                range=types.Range(
                    start=types.Position(line=line, character=col),
                    end=types.Position(line=line, character=col + 1),
                ),
                message=exc.message,
                severity=types.DiagnosticSeverity.Error,
                source="pdsl",
            )
        )
    ls.text_document_publish_diagnostics(
        types.PublishDiagnosticsParams(uri=uri, diagnostics=diagnostics)
    )


@server.feature(types.TEXT_DOCUMENT_DID_OPEN)
def did_open(ls: LanguageServer, params: types.DidOpenTextDocumentParams) -> None:
    _validate(ls, params.text_document.uri)


@server.feature(types.TEXT_DOCUMENT_DID_CHANGE)
def did_change(ls: LanguageServer, params: types.DidChangeTextDocumentParams) -> None:
    _validate(ls, params.text_document.uri)


@server.feature(
    types.TEXT_DOCUMENT_SEMANTIC_TOKENS_FULL,
    types.SemanticTokensLegend(token_types=TOKEN_TYPES, token_modifiers=[]),
)
def semantic_tokens(
    ls: LanguageServer, params: types.SemanticTokensParams
) -> types.SemanticTokens:
    doc = ls.workspace.get_text_document(params.text_document.uri)
    try:
        tree = lark_parse(doc.source)
    except ParseError:
        return types.SemanticTokens(data=[])
    return types.SemanticTokens(data=_encode(_classify(tree)))


@server.feature(types.TEXT_DOCUMENT_FORMATTING)
def formatting(
    ls: LanguageServer, params: types.DocumentFormattingParams
) -> list[types.TextEdit]:
    doc = ls.workspace.get_text_document(params.text_document.uri)
    try:
        new_text = format_source(doc.source, width=_FORMAT_WIDTH)
    except ParseError:
        return []  # never reflow a file that does not parse
    if new_text == doc.source:
        return []
    end = types.Position(line=len(doc.lines), character=0)
    full = types.Range(start=types.Position(line=0, character=0), end=end)
    return [types.TextEdit(range=full, new_text=new_text)]


def main() -> None:
    server.start_io()


if __name__ == "__main__":
    main()
