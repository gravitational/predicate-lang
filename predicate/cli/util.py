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
from jinja2 import FileSystemLoader, Environment, select_autoescape
from pathlib import Path


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


def create_policy_file(name: str, path: str):
    """
    Create policy file
    """
    # keeping "policies" as a default directory
    default_path = "policies"
    if path != "":
        default_path = path

    Path(default_path).mkdir(parents=True, exist_ok=True)

    policy = create_policy_from_template(name)

    # keeping "policies" as a default directory
    file_name = normalize_policy_name(name, "")
    with open(f"{default_path}/{file_name}.py", 'w', encoding="utf-8") as file:
        file.write(policy)


def create_policy_from_template(name: str):
    """
    updates name to fit class naming convention
    """
    class_name = normalize_policy_name(name, "class")
    policy_name = normalize_policy_name(name, "")
    values = {
        "policyclass": class_name,
        "policyname": policy_name,
        "testname": f"test_{policy_name}"
    }

    template_loader = FileSystemLoader(searchpath="./")
    template_env = Environment(loader=template_loader, autoescape=select_autoescape())
    template = template_env.get_template("template/default.txt")
    policy_file = template.render(values)

    return policy_file


def normalize_policy_name(name: str, name_type: str):
    """
    Transform whitespace, underscore and hyphen to CamelCase for classname and snake_case as default.
    """
    if name_type == "class":
        return name.strip().title().replace(" ", "").replace("-", "").replace("_", "")
    else:
        return name.strip().lower().replace(" ", "_").replace("-", "_")
