import * as vscode from 'vscode';

export function pError(err: string) {
  return vscode.window.showErrorMessage(`Predicate: ${err}`);
}

export function pSuccess(msg: string) {
  return vscode.window.showInformationMessage(`Predicate: ${msg}`);
}
