import * as assert from 'assert';
import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

import {getDocUri, activate, sleep} from '../helper';

suite('Snippet command test suite', async () => {
  vscode.window.showInformationMessage('Start snippet command tests.');

  const folderPath = vscode.workspace?.workspaceFolders[0].uri
    .toString()
    .split(':')[1];

  const snippetPath = path.join(folderPath, '.vscode/predicate.code-snippets');

  test('execute installSnippet command', async () => {
    await activate(getDocUri('test.py'));

    await installSnippet();
  });

  test('test install snippet', async () => {
    await activate(getDocUri('test.py'));

    await testinst(snippetPath);
  });

  test('test uninstall snippet', async () => {
    await activate(getDocUri('test.py'));

    await uninstallSnippet(snippetPath);
  });
});

async function testinst(snippetPath: string) {
  const dirExists = await fs.existsSync(snippetPath);
  assert.strictEqual(dirExists, true);
}

async function installSnippet() {
  await vscode.commands.executeCommand('predicate.installSnippet');
}

async function uninstallSnippet(snippetPath: string) {
  // test if uninstall removes the snippets
  await vscode.commands.executeCommand('predicate.uninstallSnippet');
  assert.strictEqual(fs.existsSync(snippetPath), false);
}
