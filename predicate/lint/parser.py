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
from typing import Any, Tuple
from runpy import run_path
from solver.teleport import Policy


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


# TODO: abstract this function into "common" package.
def get_policy(policy_file: str) -> Tuple[str, dict[str, Any]]:
    """
    Return classname and policy from given file
    """
    try:
        module = run_path(policy_file)

        class_name = ""
        for key, value in module.items():
            if hasattr(value, 'p') and isinstance(value.p, Policy):
                class_name = key

        return class_name, module[class_name].p
    except AttributeError as err:
        raise AttributeError(err) from None
    except IndentationError as err:
        raise IndentationError(err) from None
    except SyntaxError as err:
        raise SyntaxError(err) from None


def get_rules(path: str, name: str) -> dict[str, Any]:
    """Returns linter rules"""
    module = run_path(path)
    return module[name]
