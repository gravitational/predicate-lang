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


import traceback
from pathlib import Path
import yaml
from lint.parser import get_policy, get_rules
from lint.rule import NoAllow
from lint.report import Report, ErrorReport
from lint.constants import RuleCategory


class Linter:
    """Linter tests given file or directory agains various linter rules"""

    def __init__(self, policy_file_path: str):
        self.policy_file_path = policy_file_path
        self.config = self.get_lint_config()
        # Reports and error occured during lint runner should be collected here
        self.reports = []
        self.lint_errors = []
        self.policies_filepath = []

        self.collect_policy_files(policy_file_path)

    def collect_policy_files(self, policy_file_path):
        """Collect all policy files if directory is given"""
        file_or_dir = Path(policy_file_path)
        if file_or_dir.exists() is False:
            raise FileNotFoundError
        if file_or_dir.is_dir():
            for file in Path(file_or_dir).glob("*.py"):
                # collect policy files except the ones that trails with __
                # filters files or directories such as __init__, __pycache__ etc.
                if "__" not in file.stem:
                    self.policies_filepath.append(str(file))
        else:
            self.policies_filepath.append(policy_file_path)

    def get_lint_config(self):
        """Returns linter config file"""
        # TODO: remove hardcoded config file location once desired config location path is decided.
        with open("predicatelint.yml", "r", encoding="utf-8") as f:
            return yaml.safe_load(f)

    def run_lint_category(self, rule_category, policy_file_path, class_name, policy) -> str:
        """Check policy with every registered lint rules"""
        match rule_category:
            case RuleCategory.NO_ALLOW:
                try:
                    lint_rules = get_rules(self.config['rule_files'][RuleCategory.NO_ALLOW], RuleCategory.NO_ALLOW)
                    for lint_rule_description, lint_rule in lint_rules.items():
                        result = NoAllow().check(policy, lint_rule)
                        if result:
                            self.reports.append(Report(
                                RuleCategory.NO_ALLOW,
                                lint_rule_description,
                                class_name
                            ).get_report(policy_file_path))
                except AttributeError:
                    self.lint_errors.append(ErrorReport(
                        policy_file_path,
                        f"Error reading lint rule file: {self.config['rule_files'][RuleCategory.NO_ALLOW]}\n{traceback.format_exc()}"
                    ).get_report())
            case _:
                raise ValueError(f"Unsupported rule name {rule_category}")

    def run(self):
        """
        Executes configured rule category on given policy file(s).
        Returns a tuple of findings report and error.
        Exception should be handle inside main runner and reported to caller
        """
        for policy_file_path in self.policies_filepath:
            class_name, policy = get_policy(policy_file_path)
            active_rules = self.config['linter']['active_rules']
            for rule_category in active_rules:
                self.run_lint_category(
                    rule_category,
                    policy_file_path,
                    class_name,
                    policy)

        return self.reports, self.lint_errors
