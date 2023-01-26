# Predicate VS Code Extension

Auto complete, code snippets and linter for Predicate policies.

## Project Setup

- `npm install` inside project directory should install all the required dependencies.
- Code bundling is performed using webpack.
- `eslint`, `prettier` and `google gts` is used code lint and formatting.
- Typescript configuration at `tsconfig.json`.

### Dev build

1. Open `vscode` workspace
2. Inside editor, press `cmd+shift+b` to compile extension.
3. Press `cmd+shift+d` to open extension host.
4. Inside extension host, press `cmd+shift+p` to open command pellet. Type "install snippets" and you should see "Predicate: Install snippets" command available. Press the command and snippets will be installed inside `.vscode` directory of this workspace.
5. Now open a python file and type class (you should see snippet option in VS Code)

### Test

Run `make test`. This will run unit tests as well as integration test against `lsp-server`.

For manual testing using VS Code UI, you can select `Extension Test` in `Run and Debug` menu in VS Code.

## Features

### Code Snippets

Auto-completion for Predicate python classes, functions and imports.

#### Commands

Code snippets registers two commands: `extension.installSnippet` and `extension.uninstallSnippet`

### LSP Client

- Implements diagnostic API to report linter data.
