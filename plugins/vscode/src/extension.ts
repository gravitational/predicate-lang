// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import {installSnippet, uninstallSnippet} from './snippets';

// This method is called when predicate extension is activated
export function activate(context: vscode.ExtensionContext) {
  // register installSnippet command
  const installSnippetDisposable = vscode.commands.registerCommand(
    'extension.installSnippet',
    () => {
      installSnippet();
    }
  );

  context.subscriptions.push(installSnippetDisposable);

  // register activateSnippet command
  const uninstallSnippetDisposable = vscode.commands.registerCommand(
    'extension.uninstallSnippet',
    () => {
      uninstallSnippet();
    }
  );

  context.subscriptions.push(uninstallSnippetDisposable);
}

// This method is called when your extension is deactivated
export function deactivate() {}
