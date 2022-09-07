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
from collections.abc import Iterable

from . import ast


class Options(ast.Predicate):
    """
    Options apply to some allow rules if they match
    """

    max_session_ttl = ast.Duration("options.max_session_ttl")

    pin_source_ip = ast.Bool("options.pin_source_ip")

    recording_mode = ast.StringEnum(
        "options.recording_mode", set([(0, "best_effort"), (1, "strict")])
    )

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


class OptionsSet:
    """
    OptionsSet is a set of option expressions
    """

    def __init__(self, *options: Options):
        self.options = options

    def collect_like(self, other: ast.Predicate):
        return [
            o for o in self.options if len(o.symbols.intersection(other.symbols)) > 0
        ]


class Node(ast.Predicate):
    """
    Node is SSH node
    """

    login = ast.String("node.login")
    labels = ast.StringMap("node.labels")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)
        # TODO check that the predicate is complete, has listed logins

    def __and__(self, options: Options):
        """
        This is a somewhat special case, options define max session TTL,
        so this operator constructs a node predicate that contains options
        that are relevant to node.
        """
        return Node(self.expr & options.expr)


class LoginRule(ast.StringSetMap):
    """
    Login rule maps SSO identities to Teleport's traits
    """

    pass


def PolicyMap(expr):
    """
    PolicyMap is expression that evaluates to a list of
    policy names.
    """
    # TODO: evaluate that policy map always evals to string list?
    return expr


def try_login(policy_map_expr, traits_expr, policies):
    policies = {p.name: p for p in policies}
    p = ast.Predicate(policy_map_expr != ast.StringListWrapper(()))
    ret, model = p.check(ast.Predicate(traits_expr))
    if not ret:
        return ()
    out = []

    def first(depth):
        vals = policy_map_expr.traverse()
        for i in range(depth):
            vals = ast.StringList.cdr(vals)
        expr = ast.fn_string_list_first(vals)
        return model.eval(expr).as_string()

    depth = 0
    while True:
        el = first(depth)
        if el == "":
            break
        out.append(el)
        depth += 1

    mapped_policies = []
    for policy_name in out:
        mapped_policies.append(policies[policy_name])
    return PolicySet(mapped_policies)


class User:
    """
    User is a Teleport user
    """

    # name is username
    name = ast.String("user.name")

    # traits is a user trait
    traits = ast.StringMap("user.traits")


class Role:
    name = ast.String("role.name")


class Thresholds:
    approve = ast.Int("request.approve")
    deny = ast.Int("request.deny")


class Request(ast.Predicate):
    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


class Review(ast.Predicate):
    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


class Rules:
    """
    Rules are allow or deny rules
    """

    def __init__(self, *rules):
        self.rules = rules or []

    def collect_like(self, other: ast.Predicate):
        return [r for r in self.rules if r.__class__ == other.__class__]


class Policy:
    def __init__(
        self,
        name: str,
        options: OptionsSet = None,
        allow: Rules = None,
        deny: Rules = None,
    ):
        self.name = name
        if name == "":
            raise ast.ParameterError("supply a valid name")
        if allow is None and deny is None:
            raise ast.ParameterError("provide either allow or deny")
        self.allow = allow or Rules()
        self.deny = deny or Rules()
        self.options = options or OptionsSet()

    def check(self, other: ast.Predicate):
        return PolicySet([self]).check(other)

    def query(self, other: ast.Predicate):
        return PolicySet([self]).query(other)


class PolicySet:
    """
    PolicySet is a set of policies, it merges all allow and all deny rules
    from all other policies.
    """

    def __init__(self, policies: Iterable[Policy]):
        self.policies = policies

    def build_predicate(self, other: ast.Predicate) -> ast.Predicate:
        allow = []
        deny = []
        options = []
        for p in self.policies:
            allow.extend([e.expr for e in p.allow.collect_like(other)])
            # here we collect options from our policies that are mentioned in the predicate
            # we are checking against, so our options are "sticky"
            options.extend([o.expr for o in p.options.collect_like(other)])
            deny.extend([ast.Not(e.expr) for e in p.deny.collect_like(other)])

        # all options should match
        # TODO: how to deal with Teleport options logic that returns min out of two?
        # probably < equation will solve this problem
        allow_expr = None
        options_expr = None
        # if option predicgae are present, apply them as mandatory
        # to the allow expression, so allow is matching only if options
        # match as well.
        if options:
            options_expr = functools.reduce(operator.and_, options)
        if allow:
            allow_expr = functools.reduce(operator.or_, allow)
            if options:
                allow_expr = allow_expr & options_expr
        if deny:
            deny_expr = functools.reduce(operator.and_, deny)

        if not allow and not deny:
            raise ast.ParameterError("policy set is empty {}")
        pr = None
        if not deny:
            pr = ast.Predicate(allow_expr)
        elif not allow_expr:
            pr = ast.Predicate(deny_expr)
        else:
            pr = ast.Predicate(allow_expr & deny_expr)
        return pr

    def check(self, other: ast.Predicate):
        return self.build_predicate(other).check(other)

    def query(self, other: ast.Predicate):
        return self.build_predicate(other).query(other)

    def names(self):
        """
        Names returns names in the policy set
        """
        s = set()
        for p in self.policies:
            s.add(p.name)
        return s
