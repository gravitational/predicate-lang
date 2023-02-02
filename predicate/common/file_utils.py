"""
Copyright 2023 Gravitational, Inc

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

import yaml
from pathlib import Path


def get_lint_config():
    """Returns linter config file"""
    # TODO: remove hardcoded config file location once desired config location path is decided.
    # https://github.com/gravitational/predicate-lang/issues/79
    with open("predicatelint.yml", "r", encoding="utf-8") as f:
        return yaml.safe_load(f)


def get_policy_files(policy_filepath):
    """ Get policy files."""
    policy_files = []
    file_or_dir = Path(policy_filepath)
    if file_or_dir.exists() is False:
        raise FileNotFoundError
    if file_or_dir.is_dir():
        for file in Path(file_or_dir).glob("*.py"):
            # collect policy files except the ones that trails with __
            # filters files or directories such as __init__, __pycache__ etc.
            if "__" not in file.stem:
                policy_files.append(str(file))
    else:
        policy_files.append(policy_filepath)

    return policy_files
