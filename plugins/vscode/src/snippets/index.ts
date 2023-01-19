import * as vscode from 'vscode';
import * as fs from 'fs';
import * as path from 'path';

import {pError, pSuccess} from '../alerts';
import {predicateSnippet} from './snippets';

// retreives current workspace path
const folderPath = vscode.workspace?.workspaceFolders[0].uri
  .toString()
  .split(':')[1];

const vscodePath = path.join(folderPath, '.vscode');
const snippetPath = path.join(folderPath, '.vscode/predicate.code-snippets');

// install snippets inside .vscode directory
export function installSnippet() {
  // return if workspaceFolders is undefined
  if (!vscode.workspace.workspaceFolders) {
    return pError('please open a project folder first');
  }

  // assumes the opened dir is also the root vscode workspace
  fs.mkdir(vscodePath, {recursive: true}, err => {
    if (err) {
      return pError(err.toString());
    } else {
      fs.writeFile(
        snippetPath,
        JSON.stringify(predicateSnippet, null, '\t'),
        err => {
          if (err) {
            return pError('error creating snippet file');
          } else {
            pSuccess('snippets installed in this workspace!');
          }
        }
      );
    }
  });
}

// install snippets inside .vscode directory
export function uninstallSnippet() {
  // return if workspaceFolders is undefined
  if (!vscode.workspace.workspaceFolders) {
    return pError('please open a project directory first');
  }

  if (fs.existsSync(vscodePath)) {
    fs.unlink(snippetPath, err => {
      if (err) {
        return pError('no snippet file found in .vscode directory');
      }
      pSuccess('snippets removed from this workspace!');
    });

    // delete .vscode if there are not other config files
    fs.readdir(vscodePath, (err, files) => {
      if (err) {
        return pError('could not read .vscode directory in this workspace');
      }
      if (files.length === 0) {
        fs.rmdir(vscodePath, err => {
          if (err) {
            return pError('could not delete empty .vscode directory');
          }
        });
      }
    });
  }
}
