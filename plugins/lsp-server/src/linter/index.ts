/* --------------------------------------------------------------------------------------------
 * Copyright 2022 Gravitational, Inc
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 * ----------------------------------------------------------------------------------------------- */

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
  // eslint-disable-next-line @typescript-eslint/naming-convention
  code_snippet: string;
  description: string;
  file: string;
  // eslint-disable-next-line @typescript-eslint/naming-convention
  line_number: number;
  // eslint-disable-next-line @typescript-eslint/naming-convention
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
  // TODO: Remove hardcoded predicate binary path.
  // See https://github.com/gravitational/predicate-lang/issues/81
  linterExecutablePath: string = path.resolve(__dirname, '../../../predicate');

  constructor(activeDocument: TextDocument) {
    this.activeDocument = activeDocument;
  }

  // Map linter result to diagnostic object
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

  private async execLinter(linterExecutablePath: string): Promise<ExecOut> {
    const policyFile = new url.URL(this.activeDocument.uri);
    const command = `poetry run predicate lint --out=json ${policyFile.pathname}`;

    const result = await asyncExec(command, {cwd: linterExecutablePath});

    return result;

    // const result = await asyncExec(command);
  }

  public async run(
    linterExecutablePath = this.linterExecutablePath
  ): Promise<LintResult> {
    try {
      const lintResult = await this.execLinter(linterExecutablePath);

      if (lintResult.stdout) {
        const diagnosticResult = await this.linterToDiagnostic(lintResult);
        return {uri: this.activeDocument.uri, diagnostics: diagnosticResult};
      }
      if (lintResult.stderr) {
        console.log('stderr: ', lintResult.stderr);
      }
    } catch (e) {
      console.log('error: ', e);
    }
    const d: Diagnostic[] = [];
    return {uri: '', diagnostics: d};
  }
}
