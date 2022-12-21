"""
Copyright 2022 Gravitational, Inc

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
"""

import ast
from io import TextIOWrapper



class AllowVisitor(ast.NodeVisitor):
    """Collect start and end line number for allow rules"""
    def __init__(self, class_name):
        self.lineno = 0
        self.end_lineno = 0
        self.class_name = class_name

    def visit_ClassDef(self, tree: ast.ClassDef):
        if tree.name == self.class_name:
            for node in ast.walk(tree):
                if isinstance(node, ast.Assign):
                    for assign in node.value.keywords:
                        if assign.arg == "allow":
                            self.lineno = assign.lineno
                            self.end_lineno = assign.end_lineno
                        
        self.generic_visit(tree)


def get_ast_tree(code_buf: str):
    """ return ast tree"""
    return ast.parse(code_buf)


def get_code_snippet(file: TextIOWrapper, lineno, end_lineno)-> str:
    """Return code snippet from policy file"""
    return ' '.join(file.readlines()[lineno:end_lineno])