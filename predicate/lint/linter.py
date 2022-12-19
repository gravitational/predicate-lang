from runpy import run_path

from solver.teleport import User, AccessNode

import ast


class LinterMessage:
    def __init__(
        self,
        line_number: str,
        code_snippet: str,
        description=str,
        file_name= str,
        ):
        self.line_number = line_number
        self.code_snippet = code_snippet
        self.description = description
        self.file_name = file_name

    def __str__(self):
        return f"File: {self.file_name},  Line number: {self.line_number} \n Description: {self.description} \n Code: \n {self.code_snippet}"


def linter(policy_file):

    test_rule = AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            )
    module = run_path(policy_file)
    policy = module["Teleport"].p


    check = None
    try:
        check = policy.equivalent(test_rule, "allow")
    except Exception as err:
        return err

    if check[0]:
        with open(policy_file, 'r', encoding="utf-8") as file:
            filevalue = file.read()
            nodes = ast.parse(filevalue)

            line_number = 0
            for n in nodes.body:
                if isinstance(n, ast.ClassDef):
                    for b in n.body:
                        if isinstance(b, ast.Assign):
                            # print(b.value.keywords)
                            for a in b.value.keywords:
                                if a.arg == "allow":
                                    line_number = a.lineno

            file.seek(0)

            val = file.readlines()
            message = LinterMessage(
                line_number = line_number,
                code_snippet= val[line_number - 1 ]+val[line_number]+val[line_number + 1],
                description="Violated deny rules",
                file_name = policy_file
            )
            return message
    else:
        return None
        
                        
                                


 
        
    





 