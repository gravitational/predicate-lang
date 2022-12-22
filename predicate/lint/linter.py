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


def get_lint_config():
    """Returns linter config file"""
    # TODO: remove hardcoded config file location.
    with open("predicatelint.yml", "r", encoding="utf-8") as f:
        return yaml.safe_load(f)


def linter(policy_file):
    """Run linter on a given file"""
    reports = []
    class_name, policy = get_policy(policy_file)

    config = get_lint_config()
    active_rules = config['linter']['active_rules']

    for rule_type in active_rules:
        if rule_type == RuleCategory.NO_ALLOW:
            rules = get_rules(config['rule_files'][RuleCategory.NO_ALLOW], RuleCategory.NO_ALLOW)
            if rules is not None:
                for rule_description, rule in rules.items():
                    result = NoAllow().check(rule, policy)
                    if result:
                        reports.append(Report(
                            RuleCategory.NO_ALLOW,
                            rule_description,
                            policy_file,
                            class_name
                        ).get_report(policy_file))

    return reports
