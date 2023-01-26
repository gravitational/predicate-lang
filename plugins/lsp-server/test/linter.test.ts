import {Linter} from '../src/linter';
import * as path from 'path';
import {TextDocument} from 'vscode-languageserver-textdocument';

// we only want to test if, given a executable path, lsp-server can communicate with
// predicate linter.
test('test io with predicate linter', async () => {
  const testFileURI = `file:///${path.resolve(
    __dirname,
    'fixture/failing_policy.py'
  )}`;

  const doc = TextDocument.create(testFileURI, 'python', 0, '');

  const linterInstance = new Linter(doc);
  const linterExecPath = path.resolve(__dirname, '../../../predicate');
  const resultObj = await linterInstance.run(linterExecPath);

  // the file failing_policy violates "no root user" policy defined in
  // predicate linter test (/predicate/lint/test/data/no_allow.py)
  expect(resultObj?.diagnostics[0]?.message).toBe('no root users');
});
