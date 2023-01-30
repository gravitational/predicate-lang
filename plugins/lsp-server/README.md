## Predicate LSP Server

`predicate-lsp-server`

Implements [language server](https://code.visualstudio.com/api/language-extensions/language-server-extension-guide) using [vscode-language-server-node](https://github.com/microsoft/vscode-languageserver-node).

## Project Setup

- `npm install` inside project directory should install all the required dependencies.
- Code bundling is performed using webpack.
- `eslint`, `prettier` and `google gts` is used code lint and formatting.
- Typescript configuration at `tsconfig.json`.

### Dev build

- Dev build: `npm run dev`.
- Almost all dev workflow for `lsp-server` will require VS Code extension. Follow VS Code Extension setup for more details.
- Depends on predicate python program.

### Test

Run `npm test` in this directory. Jest is used for testing.

Integration test should be run from VS Code extension. Inside vscode direcotry, running `make test`.

## Features

### Diagnostic

Diagnostic data are populated using results from `$ predicate lint ...`.

Node `child_process` is used to invoke predicate cli.

- Works when policy file is opened or saved.
