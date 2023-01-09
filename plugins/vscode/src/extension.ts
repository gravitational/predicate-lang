// The module 'vscode' contains the VS Code extensibility API
// Import the module and reference it with the alias vscode in your code below
import * as vscode from 'vscode';
import {installSnippet, uninstallSnippet} from './snippets';
import {startLSPClient} from './lsp-client';
import {LanguageClient} from 'vscode-languageclient/node';

let client: LanguageClient;
/**
 * This method is called when vscode.predicate is activated
 */
export function activate(context: vscode.ExtensionContext) {
  // register installSnippet command
  const installSnippetDisposable = vscode.commands.registerCommand(
    'predicate.installSnippet',
    () => {
      installSnippet();
    }
  );

  context.subscriptions.push(installSnippetDisposable);

  // register activateSnippet command
  const uninstallSnippetDisposable = vscode.commands.registerCommand(
    'predicate.uninstallSnippet',
    () => {
      uninstallSnippet();
    }
  );

  context.subscriptions.push(uninstallSnippetDisposable);

  const client = startLSPClient();
  client.start();
}

/*
 * This method is called when your extension is deactivated
 */
export function deactivate() {
  if (!client) {
    return undefined;
  }
  return client.stop();
}
