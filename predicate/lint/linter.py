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
from common.file_utils import get_lint_config
from common.policy_utils import get_policy, get_rules
from lint.rule import NoAllow, Duplicate
from lint.report import Report, ErrorReport
from common.constants import RuleCategory


class Linter:
    """Linter tests given file or directory agains various linter rules"""

    def __init__(self, policy_filepath: str):
        self.config = get_lint_config()
        # Reports and error occured during lint runner should be collected here
        self.reports = []
        self.lint_errors = []

        self.input_policy_dir = []
        # base_policy_dir is used for duplicate policy checks
        self.base_policy_dir = []

        self.policies_to_check(policy_filepath)

    def get_policy_files(self, policy_filepath):
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

    def policies_to_check(self, policy_filepath):
        """Collect all policy files if directory is given"""
        input_files = self.get_policy_files(policy_filepath)
        self.input_policy_dir = input_files
        base_policy_dir = self.get_policy_files(self.config['policy_dir'])
        self.base_policy_dir = base_policy_dir

    def run_lint_category(self, rule_category, policy_filepath, class_name, policy):
        """Check policy with every registered lint rules in predicalint.yml"""

        match rule_category:
            case RuleCategory.NO_ALLOW:
                try:
                    lint_rules = get_rules(self.config['rule_files'][RuleCategory.NO_ALLOW], RuleCategory.NO_ALLOW)
                    for lint_rule_description, lint_rule in lint_rules.items():
                        result = NoAllow().check(policy, lint_rule)
                        if result:
                            return (Report(
                                RuleCategory.NO_ALLOW,
                                lint_rule_description,
                                class_name,
                                {}
                            ).get_report(policy_filepath))
                except AttributeError:
                    self.lint_errors.append(ErrorReport(
                        policy_filepath,
                        f"Error reading lint rule file: {self.config['rule_files'][RuleCategory.NO_ALLOW]}\n{traceback.format_exc()}"
                    ).get_report())
            case RuleCategory.DUPLICATE:
                try:
                    result = Duplicate(policy_filepath).check(policy, policy_filepath, self.base_policy_dir)
                    if result:
                        report_list = []
                        for report in result:
                            report_list.append(Report(
                                RuleCategory.DUPLICATE,
                                report.findings,
                                class_name,
                                {"is_name": report.is_name}
                            ).get_report(policy_filepath))

                        return {
                            "category": RuleCategory.DUPLICATE,
                            "findings": report_list
                        }
                except AttributeError:
                    self.lint_errors.append(ErrorReport(
                        policy_filepath,
                        f"Error querying duplicate policies\n{traceback.format_exc()}"
                    ).get_report())
            case _:
                raise ValueError(f"Unsupported rule name {rule_category}")

    def run(self):
        """
        Executes configured rule category on given policy file(s).
        Returns a tuple of findings report and error.
        Exception should be handle inside main runner and reported to caller
        """

        final_report: dict[str, list] = {}
        for policy_filepath in self.input_policy_dir:
            class_name, policy = get_policy(policy_filepath)
            active_rules = self.config['linter']['active_rules']
            report = []

            for rule_category in active_rules:
                result = self.run_lint_category(
                    rule_category,
                    policy_filepath,
                    class_name,
                    policy)
                if result:
                    report.append(result)
                    final_report[policy_filepath] = report

        return final_report, self.lint_errors
