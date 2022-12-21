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

from lint.ast import AllowVisitor, get_ast_tree, get_code_snippet
from lint.report import LinterMessage



class ForbidAllow():
    """Checks if Policy contains spcefic rules denied by administrator"""
    def __init__(self, class_name, description):
        self.lineno = 0
        self.end_lineno = 0
        self.class_name = class_name
        self.description = description


    def check(self, rule, policy, file_name ):
        """check predicate"""
        check = None
        try:
            check = policy.equivalent(rule, "allow")
            return check[0], self.get_report(file_name)
        except Exception as err:
            return False, err
          
    def get_report(self, file_name):
        """ Collect start and end line, along with code snippet using AST """
        with open(file_name, 'r', encoding="utf-8") as file:
            data = file.read()
            tree = get_ast_tree(data)
            visitor = AllowVisitor(self.class_name)
            visitor.visit(tree)
            self.lineno, self.end_lineno = visitor.lineno, visitor.end_lineno

            file.seek(0)
            code_snippet = get_code_snippet(file, self.lineno, self.end_lineno)

            return LinterMessage(
                        line_number = self.lineno,
                        code_snippet= f"{code_snippet}",
                        description= self.description,
                        file_name = file_name
                    )


