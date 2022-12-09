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
import os
from jinja2 import FileSystemLoader, Environment, select_autoescape

def get_classname(policyfile: str):
    """
    Get class name from policy file.
    """
    with open(policyfile, 'r', encoding="utf-8") as file:
        return parse_classname(file.read())

def parse_classname(policy: str):
    """
    Parse class name using ast. Expects one class per poliy file.
    """
    parsed = ast.parse(policy)
    nodes = ast.walk(parsed)
    for node in nodes:
        if isinstance(node, ast.ClassDef):
            return node.name
    return ""

def create_dir_if_not_exist(path: str):
    """
    Create policies directory
    """
    does_exist = os.path.exists(path)
    if not does_exist:
        os.makedirs(path)


def create_policy_from_template(name: str):
    """
    updates name to fit class naming convention
    """
    values = {
        "policyclass": name.capitalize(),
        "policyname": name.lower(),
        "testname": f"test_{name.lower()}"
    }

    template_loader = FileSystemLoader(searchpath="./")
    template_env = Environment(loader=template_loader, autoescape=select_autoescape())
    template = template_env.get_template("template/default.txt")
    policy_file = template.render(values)

    return policy_file
