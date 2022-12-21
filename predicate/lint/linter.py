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

from runpy import run_path
import yaml

from cli.policy_utils import get_policy
from lint.rule import ForbidAllow
from lint.report import LinterMessage



def get_lint_config():
    """Returns linter config file"""
    #TODO: remove hardcoded config file location 
    with open("predicatelint.yml", "r", encoding="utf-8") as f:
        return yaml.safe_load(f)

def get_rule_file():
    """Returns linter rule files"""
    #TODO: should return different rule files for different linter types
    config = get_lint_config()
    module = run_path(config["config_files"]["disallow_rules"])
    rules = module['forbid_allow_rules']
    return rules
    
def linter(policy_file):
    """Run linter on a given file"""
    reports: list[LinterMessage] = []
    class_name, policy = get_policy(policy_file)

    rules = get_rule_file()

    for rule_description, rule in rules.items():
        report = ForbidAllow(class_name, rule_description).check(rule, policy, policy_file)
        if report[0]:
            reports.append(report[1])
  
    return reports




