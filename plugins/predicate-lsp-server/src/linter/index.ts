import {exec} from 'child_process';
import * as path from 'path';
import * as url from 'url';
import {promisify} from 'util';
import {Diagnostic, DiagnosticSeverity} from 'vscode-languageserver/node';

import {TextDocument} from 'vscode-languageserver-textdocument';

const asyncExec = promisify(exec);

/**
 * LinterResult is a structure of JSON data returned by predicate linter.
 * names are snake_case to match with linter result value.
 */
interface LinterResult {
  category: string;
  code_snippet: string;
  description: string;
  file: string;
  line_number: number;
  line_end_number: number;
}

interface LintResult {
  uri: string;
  diagnostics: Diagnostic[];
}

interface ExecOut {
  stdout: string;
  stderr: string;
}

/**
 * Linter runs `$ predicate lint` command on the given file and returns diagnostic data.
 */
export class Linter {
  activeDocument: TextDocument;

  constructor(activeDocument: TextDocument) {
    this.activeDocument = activeDocument;
  }

  private async linterToDiagnostic(result: ExecOut): Promise<Diagnostic[]> {
    const problems: [LinterResult] = JSON.parse(result?.stdout);
    const diagnostics: Diagnostic[] = [];
    problems.forEach(e => {
      const diagnostic: Diagnostic = {
        severity: DiagnosticSeverity.Error,
        range: {
          start: {line: e.line_number, character: e.line_number},
          end: {line: e.line_end_number - 1, character: e.line_end_number - 1},
        },
        message: `${e.description}`,
        source: `| Predicate: ${e.category}`,
      };

      diagnostic.relatedInformation = [
        {
          location: {
            uri: this.activeDocument.uri,
            range: Object.assign({}, diagnostic.range),
          },
          message: 'Consider using less privileged rule.',
        },
      ];

      diagnostics.push(diagnostic);
    });

    return diagnostics;
  }

  private async execLinter(): Promise<ExecOut> {
    const finalPath = new url.URL(this.activeDocument.uri);
    const linterPath = path.resolve(__dirname, '../../../predicate');

    const command = `poetry run predicate lint --out=json ${finalPath.pathname}`;
    const result = await asyncExec(command, {cwd: linterPath});
    return result;
  }

  public async run(): Promise<LintResult> {
    try {
      const lintResult = await this.execLinter();
      if (lintResult.stdout) {
        const diagnosticResult = await this.linterToDiagnostic(lintResult);
        return {uri: this.activeDocument.uri, diagnostics: diagnosticResult};
      }
    } catch (e) {
      console.log('error: ', e);
    }
    const d: Diagnostic[] = [];
    return {uri: '', diagnostics: d};
  }
}
