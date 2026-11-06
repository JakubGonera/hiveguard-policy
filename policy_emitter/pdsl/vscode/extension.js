"use strict";

// Policy DSL extension: launches `python -m pdsl.lsp.server`.
// Paths are auto-detected so a fresh clone works without per-machine settings.

const fs = require("fs");
const path = require("path");
const { workspace, window } = require("vscode");
const { LanguageClient, TransportKind } = require("vscode-languageclient/node");

let client;

/** Locate the `policy_emitter` directory (the one that contains `pdsl/`). */
function findEmitterDir(extensionPath) {
  const candidates = [
    // Dev mode (F5): the extension lives at <policy_emitter>/pdsl/vscode.
    path.resolve(extensionPath, "..", ".."),
  ];
  for (const folder of workspace.workspaceFolders || []) {
    const root = folder.uri.fsPath;
    candidates.push(
      root,
      path.join(root, "policy_emitter"),
      path.join(root, "trustnobpf", "policy_emitter"),
    );
  }
  for (const dir of candidates) {
    if (fs.existsSync(path.join(dir, "pdsl", "lsp", "server.py"))) {
      return dir;
    }
  }
  return null;
}

/** Pick the interpreter: explicit setting, then the repo venv, then uv. */
function resolveServer(emitterDir) {
  const configured = workspace.getConfiguration("pdsl").get("pythonPath");
  if (configured) {
    return { command: configured, args: ["-m", "pdsl.lsp.server"] };
  }
  const venv =
    process.platform === "win32"
      ? path.join(emitterDir, ".venv", "Scripts", "python.exe")
      : path.join(emitterDir, ".venv", "bin", "python");
  if (fs.existsSync(venv)) {
    return { command: venv, args: ["-m", "pdsl.lsp.server"] };
  }
  // No venv yet: let uv create/sync one on the fly.
  return { command: "uv", args: ["run", "python", "-m", "pdsl.lsp.server"] };
}

function activate(context) {
  const emitterDir =
    workspace.getConfiguration("pdsl").get("cwd") ||
    findEmitterDir(context.extensionPath);

  if (!emitterDir) {
    window.showErrorMessage(
      "pdsl: could not locate the policy_emitter directory. " +
        'Open the repo as a workspace folder, or set "pdsl.cwd" in settings.',
    );
    return;
  }

  const { command, args } = resolveServer(emitterDir);
  const formatWidth = workspace.getConfiguration("pdsl").get("formatWidth");
  const env = { ...process.env };
  if (formatWidth) {
    env.PDSL_FORMAT_WIDTH = String(formatWidth);
  }
  const serverOptions = {
    command,
    args,
    options: { cwd: emitterDir, env },
    transport: TransportKind.stdio,
  };
  const clientOptions = {
    documentSelector: [{ scheme: "file", language: "policy" }],
  };

  client = new LanguageClient(
    "pdsl",
    "Policy DSL",
    serverOptions,
    clientOptions,
  );
  client.start();
}

function deactivate() {
  return client ? client.stop() : undefined;
}

module.exports = { activate, deactivate };
