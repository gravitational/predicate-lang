import * as assert from 'assert';
import * as vscode from 'vscode';
import {activate, getDocUri, sleep} from '../../helper';

const failingPolicy = `# pylint: skip-file
from solver.teleport import AccessNode, Policy, Rules, User


class Teleport:
    p = Policy(
        name="access",
        allow=Rules(
            AccessNode(User.name == "root")
        )
    )
`;

const passingPolicy = `# pylint: skip-file
from solver.teleport import AccessNode, Policy, Rules, User


class Teleport:
    p = Policy(
        name="access",
        allow=Rules(
            AccessNode(User.name == "user")
        )
    )
`;

// Tests connection with lsp-server as well as diagnostic data.
suite('Test Diagnostics', async () => {
  const expectedFailingDiagnostics: vscode.Diagnostic[] = [
    {
      message: 'no root users',
      range: toRange(8, 8, 9, 9),
      severity: vscode.DiagnosticSeverity.Error,
      source: '| Predicate:',
    },
  ];

  test('Get diagnostics on failing test (on file open)', async () => {
    const docUri = getDocUri('failing_test.py');
    await activate(docUri);
    await testFailing(docUri, expectedFailingDiagnostics);
  });

  test('Update diagnostics on resolved issue', async () => {
    const docUri = getDocUri('resolve_failing_test.py');
    await activate(docUri);
    await testPassing(docUri);
  });
});

function toRange(sLine: number, sChar: number, eLine: number, eChar: number) {
  const start = new vscode.Position(sLine, sChar);
  const end = new vscode.Position(eLine, eChar);
  return new vscode.Range(start, end);
}

async function testFailing(
  docUri: vscode.Uri,
  expectedDiagnostics: vscode.Diagnostic[]
) {
  const actualDiagnostics = vscode.languages.getDiagnostics(docUri);

  assert.deepStrictEqual(actualDiagnostics.length, expectedDiagnostics.length);

  expectedDiagnostics.forEach((expectedDiagnostic, i) => {
    const actualDiagnostic = actualDiagnostics[i];
    assert.strictEqual(actualDiagnostic.message, expectedDiagnostic.message);
    assert.deepStrictEqual(actualDiagnostic.range, expectedDiagnostic.range);
    assert.strictEqual(actualDiagnostic.severity, expectedDiagnostic.severity);
  });
}

async function testPassing(docUri: vscode.Uri) {
  await vscode.workspace.fs.writeFile(
    docUri,
    Buffer.from(passingPolicy, 'utf-8')
  );

  await vscode.workspace.saveAll();
  await sleep(2000);
  const zeroDiagnostic = vscode.languages.getDiagnostics(docUri);
  assert.deepStrictEqual(zeroDiagnostic.length, 0);

  // update policy to default state (failing)
  await vscode.workspace.fs.writeFile(
    docUri,
    Buffer.from(failingPolicy, 'utf-8')
  );
}

// async function writePolicy(passing: boolean) {
//   const file = getDocPath('failing_test.py');
//   await fs.writeFileSync(file, passing ? passingPolicy : failingPolicy);
// }
