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


import yaml
from cli.policy_utils import get_policy
from lint.rule import NoAllow, get_rules
from lint.report import Report
from lint.constants import RuleCategory

from pathlib import Path


class Linter:
    """Linter tests given file or directory agains various linter rules"""

    def __init__(self, policy_file_path: str):
        self.policy_file_path = policy_file_path
        self.config = self.get_lint_config()
        self.policies_path = []

        self.collect_policies(policy_file_path)

    def collect_policies(self, policy_file_path):
        """Collect all policy files if directory is given"""
        file_or_dir = Path(policy_file_path)
        if file_or_dir.is_dir():
            for file in Path(file_or_dir).glob("*.py"):
                # collect policy files except the ones that trails with __
                # filters files or directories such as __init__, __pycache__ etc.
                if "__" not in file.stem:
                    self.policies_path.append(str(file))
        else:
            self.policies_path.append(policy_file_path)

    def get_lint_config(self):
        """Returns linter config file"""
        # TODO: remove hardcoded config file location.
        with open("predicatelint.yml", "r", encoding="utf-8") as f:
            return yaml.safe_load(f)

    def run(self):
        """Main linter runner"""
        reports = []

        for policy_path in self.policies_path:
            class_name, policy = get_policy(policy_path)

            active_rules = self.config['linter']['active_rules']

            for rule_type in active_rules:
                if rule_type == RuleCategory.NO_ALLOW:
                    lint_rules = get_rules(self.config['rule_files'][RuleCategory.NO_ALLOW], RuleCategory.NO_ALLOW)
                    if lint_rules is not None:
                        for rule_description, rule in lint_rules.items():
                            result = NoAllow().check(rule, policy)
                            if result:
                                reports.append(Report(
                                    RuleCategory.NO_ALLOW,
                                    rule_description,
                                    class_name
                                ).get_report(policy_path))

        return reports
