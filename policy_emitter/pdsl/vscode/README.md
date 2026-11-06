# Policy DSL - VSCode extension

Syntax highlighting and live parse diagnostics for `.pol` files, backed by the
`pdsl` language server.

## What it provides
- A TextMate grammar for baseline highlighting (works offline, no server).
- An LSP client that launches `python -m pdsl.lsp.server`, which adds:
  - parse-error diagnostics (red squiggles at the offending line/column),
  - semantic tokens that distinguish types, variables, predicates and
    parameters - a distinction a TextMate grammar cannot make.

The extension is plain JavaScript - there is no build/compile step.

## Setup (one time, after cloning)
```
cd policy_emitter            && uv sync       # Python deps (lark, pygls)
cd policy_emitter/pdsl/vscode && npm install   # the vscode-languageclient dep
```

## Install (recommended: symlink)
Run once from the `policy_emitter` directory:
```
ln -s "$(pwd)/pdsl/vscode" ~/.vscode/extensions/pdsl-0.1.0
```
Then reload VSCode (`Reload Window`, or restart). The extension is now active
in every window for any `.pol` file.

Because it is a symlink to the repo, the extension always runs the live
files. After changing the grammar, the server, or the TextMate grammar, just
`Reload Window` - no repackaging, no reinstalling.

Uninstall: `rm ~/.vscode/extensions/pdsl-0.1.0`.

## Develop the extension (F5)
To hack on `extension.js` itself: open `policy_emitter/pdsl/vscode/` as a
folder in VSCode and press **F5**. This opens an isolated "Extension
Development Host" window with the extension loaded - useful for iterating on
the client without touching your main install.

## Path resolution
The extension locates things in this order:
1. `policy_emitter` dir: the `pdsl.cwd` setting, else relative to the
   extension, else a scan of open workspace folders.
2. Interpreter: the `pdsl.pythonPath` setting, else `<policy_emitter>/.venv`,
   else `uv run` (which creates/syncs the env on demand).

Both settings are optional overrides - only needed if auto-detection fails.
Check `View -> Output -> Policy DSL` for the server log if diagnostics do not
appear.
