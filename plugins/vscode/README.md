# Predicate VS Code Extension

Auto complete, code snippets and linter for Predicate policies.

https://user-images.githubusercontent.com/10177602/210737921-d127bef0-50a8-4071-8495-b27c396aef81.mp4


## Project Setup

- `npm install` inside project directory should install all the required dependencies.
- Code bundling is performed using webpack.
- `eslint` and `google gts` is used code lint and formatting.
- Typescript configuration at `tsconfig.json`.

## Features

### Code Snippets

#### Commands

Code snippets registers two commands: `extension.installSnippet` and `extension.uninstallSnippet`

#### Working

1. Open `vscode` workspace
2. Inside editor, press `cmd+shift+b` to compile extension.
3. Press `cmd+shift+d` to open extension host.
4. Inside extension host, press `cmd+shift+p` to open command pellet. Type "install snippets" and you should see "Predicate: Install snippets" command available. Press the command and snippets will be installed inside `.vscode` directory of this workspace.
5. Now open a python file and type class (you should see snippet option in VS Code)
