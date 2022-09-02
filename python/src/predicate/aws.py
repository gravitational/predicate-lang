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

import functools
import operator
from typing import Final

from . import ast, regex
from .errors import ParameterError

# Convert AWS policies to predictate expression.
# It's not that the policy that should be modeled,
# it's the action against resource that should be modeled,
# AWS policy should be converted to predicate.
# Because it's not AWS policy that should be introspected, but action.
# AWS policy is meta?

# AWS Docs
#
# * Policies - https://docs.aws.amazon.com/IAM/latest/UserGuide/access_policies.html#access_policy-types
# * Eval Logic - https://docs.aws.amazon.com/IAM/latest/UserGuide/reference_policies_evaluation-logic.html
# * Policy elements - https://docs.aws.amazon.com/IAM/latest/UserGuide/reference_policies_elements_resource.html
# * Boundaries - https://docs.aws.amazon.com/IAM/latest/UserGuide/access_policies_boundaries.html
# * Delegation - https://docs.aws.amazon.com/IAM/latest/UserGuide/tutorial_cross-account-with-roles.html
#

ALLOW: Final[str] = "Allow"
DENY: Final[str] = "Deny"
EFFECT: Final[str] = "Effect"
STATEMENT: Final[str] = "Statement"
RESOURCE: Final[str] = "Resource"
ACTION: Final[str] = "Action"


class Action:
    resource = ast.String("action.resource")
    action = ast.String("action.action")


def policy(p: dict):
    statements = p[STATEMENT]
    # convert a single statement into a list
    if isinstance(statements, dict):
        statements = [statements]

    allow_statements = [statement(s) for s in statements if s[EFFECT] == ALLOW]
    deny_statements = [statement(s) for s in statements if s[EFFECT] == DENY]
    if not allow_statements and not deny_statements:
        raise ParameterError("fix the empty policy by adding some statements")
    if not deny_statements:
        return functools.reduce(operator.or_, allow_statements)
    if not allow_statements:
        return functools.reduce(operator.and_, deny_statements)

    # any allow statement could match and no deny statements should match
    return functools.reduce(operator.or_, allow_statements) & functools.reduce(
        operator.and_, deny_statements
    )


def statement(p: dict):
    # statement converts a policy to predicate expression
    allow = False
    if p[EFFECT] == ALLOW:
        allow = True
    elif p[EFFECT] == DENY:
        allow = False
    else:
        raise ParameterError("unsupported effect", p[EFFECT])

    resources = p[RESOURCE]
    if isinstance(resources, str):
        resources = [resources]
    actions = p[ACTION]
    if isinstance(actions, str):
        actions = [actions]

    expr = regex.tuple(_to_regex(r) for r in resources).matches(
        Action.resource
    ) & regex.tuple(_to_regex(a) for a in actions).matches(Action.action)
    if not allow:
        expr = ast.Not(expr)

    return expr


def _is_regex(v: str):
    # tests if it's AWS specific regexp that only has wildcards so far
    return "*" in v


def _parse_regex(v: str):
    return regex.parse(_to_regex(v))


def _to_regex(v: str):
    return v.replace("*", ".*")
