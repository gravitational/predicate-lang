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

import {
  createConnection,
  DidChangeConfigurationNotification,
  InitializeParams,
  InitializeResult,
  ProposedFeatures,
  TextDocuments,
  TextDocumentSyncKind,
} from 'vscode-languageserver/node';

import {TextDocument} from 'vscode-languageserver-textdocument';
import {Linter} from './linter';

// Create a connection for the server, using Node's IPC as a transport.
// Also include all preview / proposed LSP features.
const connection = createConnection(ProposedFeatures.all);

// Create a simple text document manager.
const documents: TextDocuments<TextDocument> = new TextDocuments(TextDocument);

let hasConfigurationCapability = false;
let hasWorkspaceFolderCapability = false;

connection.onInitialize((params: InitializeParams) => {
  const capabilities = params.capabilities;

  // Does the client support the `workspace/configuration` request?
  // If not, we fall back using global settings.
  hasConfigurationCapability = !!(
    capabilities.workspace && !!capabilities.workspace.configuration
  );
  hasWorkspaceFolderCapability = !!(
    capabilities.workspace && !!capabilities.workspace.workspaceFolders
  );

  const result: InitializeResult = {
    capabilities: {
      textDocumentSync: TextDocumentSyncKind.Incremental,
    },
  };
  if (hasWorkspaceFolderCapability) {
    result.capabilities.workspace = {
      workspaceFolders: {
        supported: true,
      },
    };
  }
  return result;
});

connection.onInitialized(() => {
  if (hasConfigurationCapability) {
    // Register for all configuration changes.
    connection.client.register(
      DidChangeConfigurationNotification.type,
      undefined
    );
  }
  if (hasWorkspaceFolderCapability) {
    connection.workspace.onDidChangeWorkspaceFolders(() => {
      connection.console.log('Workspace folder change event received.');
    });
  }
});

// The LSP server settings
interface LSPServerSetting {
  maxNumberOfProblems: number;
}

// Cache the settings of all open documents
const documentSettings: Map<string, Thenable<LSPServerSetting>> = new Map();

connection.onDidChangeConfiguration(() => {
  if (hasConfigurationCapability) {
    // Reset all cached document settings
    documentSettings.clear();
  }
});

// Send the computed diagnostics to VSCode.
async function sendDiagnostics(document: TextDocument) {
  const linterInstance = new Linter(document);
  const result = await linterInstance.run();

  // add linter result to connection diagnostics.
  connection.sendDiagnostics(result);
}

// The content of a text document has changed. This event is emitted
// when the text document first opened or when its content has changed.
documents.onDidOpen(async change => {
  await sendDiagnostics(change.document);
});

documents.onDidSave(async change => {
  await sendDiagnostics(change.document);
});

documents.onDidChangeContent(async change => {
  await sendDiagnostics(change.document);
});

// Only keep settings for open documents
documents.onDidClose(e => {
  documentSettings.delete(e.document.uri);
});

// Make the text document manager listen on the connection
// for open, change and close text document events
documents.listen(connection);

// Listen on the connection
connection.listen();
