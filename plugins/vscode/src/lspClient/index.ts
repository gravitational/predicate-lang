import * as path from 'path';

import {
  LanguageClient,
  LanguageClientOptions,
  ServerOptions,
  TransportKind,
} from 'vscode-languageclient/node';

export function startLSPClient(): LanguageClient {
  const serverModule = path.resolve(
    __dirname,
    '../../lsp-server/dist/server.js'
  );

  // The debug options for the server
  // --inspect=6009: runs the server in Node's Inspector mode so VS Code can attach to the server for debugging
  const debugOptions = {execArgv: ['--nolazy', '--inspect=6009']};

  // If the extension is launched in debug mode then the debug server options are used
  // Otherwise the run options are used
  const serverOptions: ServerOptions = {
    run: {module: serverModule, transport: TransportKind.ipc},
    debug: {
      module: serverModule,
      transport: TransportKind.ipc,
      options: debugOptions,
    },
  };

  // Options to control the language client
  const clientOptions: LanguageClientOptions = {
    // Register the server for python files
    documentSelector: [{scheme: 'file', language: 'python'}],
  };

  // Create the language client and start the client.
  const client = new LanguageClient(
    'predicateLSPClient',
    'Predicate LSP Client',
    serverOptions,
    clientOptions
  );

  // Start the client. This will also launch the server
  client.start();

  return client;
}
