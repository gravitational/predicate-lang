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

from dataclasses import dataclass
from typing import List
from pathlib import PurePath
from common.policy_utils import get_policy
from solver.errors import ParameterError
from solver.teleport import build_predicate

from common.constants import PredicateExpr


class NoAllow():
    """Checks if Policy contains spcefic rules denied by administrator"""

    def check(self, policy, lint_rule):
        """check predicate"""
        try:
            check = policy.equivalent(lint_rule, PredicateExpr.ALLOW, PredicateExpr.COLLECT_ALL)
            return check[0]
        except ParameterError:
            return False


@dataclass
class DuplicateRule:

    def __init__(
        self,
        matched_policies: List[str],
        findings: str,
        is_name: bool,
    ):
        self.matched_policies = matched_policies
        self.findings = findings
        self.is_name = is_name


@dataclass
class DuplicateRules:
    policy: DuplicateRule


class Duplicate():
    """
    Checks if a policy matches existing policy.
    1. Checks duplicate policy name.
    2. Checks duplicate policy rule.
    """

    def __init__(self, policy_filepath: str):
        self.duplicates: DuplicateRules = []
        self.dupe_name_files = [policy_filepath]

    def policy_matcher(self, policy1, policy2) -> bool:
        """
        Check policy using z3.equivalent.
        We will individually check each allow, options and deny rules
        and return false if one of them is unequal
        """
        try:

            policy2_expr = build_predicate([policy2], [], policy2.loud, PredicateExpr.ALL, PredicateExpr.COLLECT_ALL)
            check = policy1.equivalent(policy2_expr, PredicateExpr.ALL, PredicateExpr.COLLECT_ALL)

            return check[0]

        except ParameterError as err:
            print("caught ParameterError", str(err))
            return False
        except AttributeError:
            print("catching attribue error")
            return False

    def check(self, ppolicy, ppolicy_filepath, policies_filepath):
        """check predicate"""
        dupe: DuplicateRule = []
        try:
            # get policy from all the files
            for spolicy_filepath in policies_filepath:
                if PurePath(ppolicy_filepath).name != PurePath(spolicy_filepath).name:
                    _, spolicy = get_policy(spolicy_filepath)

                    if (ppolicy.name == spolicy.name):
                        self.dupe_name_files.append(spolicy_filepath)
                        findings = f"Duplicate policy name in files {self.dupe_name_files}"
                        dupe.append(DuplicateRule(self.dupe_name_files, findings, True))

                    z3equal = self.policy_matcher(ppolicy, spolicy)

                    if (z3equal):
                        self.dupe_name_files.append(spolicy_filepath)
                        findings = f"Duplicate policy rule in files {self.dupe_name_files}"
                        dupe.append(DuplicateRule(self.dupe_name_files, findings, False))

            return dupe

        except ParameterError:
            return False
