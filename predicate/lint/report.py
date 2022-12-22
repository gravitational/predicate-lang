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

from io import TextIOWrapper
from lint.ast import get_ast_tree, AllowVisitor
from lint.constants import RuleCategory


def get_code_snippet(file: TextIOWrapper, lineno, end_lineno) -> str:
    """Return code snippet from policy file.
    We want (lineno - 1) to get full Rule snippet
    """
    # TODO: Policy file will always be more than 2 lines of python code?
    return ' '.join(file.readlines()[lineno - 1:end_lineno])


class Report:
    """Reports linter result"""

    def __init__(
        self,
        rule_category: str,
        description: str,
        class_name: str,
    ):
        self.rule_category = rule_category
        self.description = description
        self.class_name = class_name
        self.lineno = 0
        self.end_lineno = 0
        self.code_snippet = ""

    def get_report(self, file_name):
        """ Collect start and end line, along with code snippet using AST """
        with open(file_name, 'r', encoding="utf-8") as file:
            data = file.read()
            tree = get_ast_tree(data)
            visitor = None
            if self.rule_category == RuleCategory.NO_ALLOW:
                visitor = AllowVisitor(self.class_name)
            visitor.visit(tree)
            self.lineno, self.end_lineno = visitor.lineno, visitor.end_lineno

            file.seek(0)
            self.code_snippet = get_code_snippet(file, self.lineno, self.end_lineno)

            return f"Rule Category: {self.rule_category} \nFile: {file_name}, Line number: {self.lineno} \nDescription: {self.description} \nCode: \n {self.code_snippet}"
