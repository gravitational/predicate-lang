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

# To allow using class type inside class:
# https://github.com/python/mypy/issues/3661#issuecomment-647945042
from __future__ import annotations

import functools
import operator
import re
import typing
from collections.abc import Iterable
from enum import Enum

import z3

from . import ast
from .errors import ParameterError


def scoped(cls):
    cls.scope = re.sub(r"([a-z])([A-Z])", r"\1_\2", cls.__name__).lower()
    return cls


class Options:
    """
    Options is a set of option expressions.
    """

    def __init__(self, *options):
        self.option_names: set[str] = set()
        self.options: list[ast.Predicate] = []

        # check that:
        # - each option is irreducible
        # - each option is not duplicated
        for o in options:
            if not isinstance(o, (ast.Eq, ast.Lt, ast.Le)):
                raise ParameterError("each option predicate should only contain ==, < and <= inequalities: {}".format(o))

            if isinstance(o.L, ast.LeqDuration) and o.L.name == Option.session_ttl.name:
                self.__add_option__(Option.session_ttl.name, o)
            elif isinstance(o.L, ast.Bool) and o.L.name == Option.allow_agent_forwarding.name:
                self.__add_option__(Option.allow_agent_forwarding.name, o)
            elif isinstance(o.L, ast.LeqOrderedEnum) and o.L.name == Option.session_recording_mode.name:
                self.__add_option__(Option.session_recording_mode.name, o)
            else:
                raise ParameterError("unrecognized option: {}".format(o))

    def __add_option__(self, name: str, option):
        """
        add option adds a new option.
        If the option has already been added, an error is raised.
        """
        if name in self.option_names:
            raise ParameterError("Found duplicated option: {}".format(name))
        self.option_names.add(name)
        self.options.append(ast.Predicate(option))

    def empty(self):
        """
        empty returns true if the option set is empty.
        """
        return len(self.options) == 0

    def set_defaults(self):
        """
        set defaults sets options defaults.
        """
        defaults = [
            (Option.session_ttl.name, Option.session_ttl <= ast.Duration.new(hours=30)),
            (Option.allow_agent_forwarding.name, Option.allow_agent_forwarding == False),
            (Option.session_recording_mode.name, Option.session_recording_mode == "strict")
        ]
        for option_name, default in defaults:
            if not option_name in self.option_names:
                self.__add_option__(option_name, default)

    def build_predicate(self) -> ast.Predicate:
        """
        build predicate returns a predicate with all options combined with logical AND.
        If the option set is empty, an error is raised.
        """
        if self.empty():
            raise ParameterError("cannot build predicate for empty option set")
        
        options_expr = functools.reduce(operator.and_, [o.expr for o in self.options])
        return ast.Predicate(options_expr)

    def with_predicate(self, other: ast.Predicate) -> ast.Predicate:
        """
        with predicate returns a predicate that is the logical AND of `other` and the predicate of this option set.
        If the option set is empty, `other` is returned.
        """
        if self.empty():
            return other
        else:
            return other & self.build_predicate()


class Option:
    """
    Option is a Teleport option.
    """

    session_ttl = ast.LeqDuration("option.session_ttl")

    allow_agent_forwarding = ast.Bool("option.allow_agent_forwarding")

    session_recording_mode = ast.LeqOrderedEnum(
        "option.session_recording_mode", [(0, "strict"), (1, "best_effort")]
    )


@scoped
class AccessNode(ast.Predicate):
    """
    AccessNode defines the permission to access an SSH node.
    """

    login = ast.String("access_node.login")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)
        # TODO check that the predicate is complete, has listed logins


class Node:
    """
    Node is an SSH node.
    """

    # labels are the node labels
    labels = ast.StringMap("node.labels")


class LoginRule(ast.StringSetMap):
    """
    Login rule maps SSO identities to Teleport's traits.
    """

    pass


def PolicyMap(expr):
    """
    PolicyMap is expression that evaluates to a list of
    policy names.
    """
    try:
        sort = expr.traverse().sort()
    except z3.Z3Exception as exc:
        if str(exc) == "sort mismatch":
            raise ParameterError(
                "policy map should eval to string list, got expression returning different sort types"
            )
        raise
    if sort != ast.StringListSort:
        raise ParameterError(
            "policy map should eval to string list, got: {}".format(sort)
        )
    return expr


def try_login(policy_map_expr, traits_expr):
    p = ast.Predicate(policy_map_expr != ast.StringTuple(()))
    ret = p.check(ast.Predicate(traits_expr))
    if not ret.solves:
        return ()
    out = []

    def first(depth):
        vals = policy_map_expr.traverse()
        for i in range(depth):
            vals = ast.StringListSort.cdr(vals)
        expr = ast.fn_string_list_first(vals)
        return ret.model.eval(expr).as_string()

    depth = 0
    while True:
        el = first(depth)
        if el == "":
            break
        out.append(el)
        depth += 1
    return set(out)


def map_policies(policy_names, policies):
    policies = {p.name: p for p in policies}
    mapped_policies = []
    for policy_name in policy_names:
        mapped_policies.append(policies[policy_name])
    return PolicySet(mapped_policies)


def reviews(*roles: tuple):
    """
    Reviews converts qualified reviews into a list ("review", "review")
    reviews((devs, expr)) -> ("review")
    """

    def iff(iterator):
        try:
            role, expr = next(iterator)
        except StopIteration:
            return ast.StringTuple(())
        else:
            return ast.If(
                # this is to collect all subexpressions related to review, if any
                role.build_predicate(Review(ast.BoolLiteral(True))).expr,
                ast.StringTuple.cons("review", iff(iterator)),
                iff(iterator),
            )

    return iff(iter(roles))


class User:
    """
    User is a Teleport user.
    """

    # name is username
    name = ast.String("user.name")

    # traits is a map of user traits
    traits = ast.StringSetMap("user.traits")

    def __init__(self, prefix):
        self.name = ast.String("{}.name".format(prefix))
        self.traits = ast.StringSetMap("{}.traits".format(prefix))


@scoped
class JoinSession(ast.Predicate):
    """
    JoinSession defines the permission to join a session.

    This predicate models `join_sessions`.
    Full documentation here: https://goteleport.com/docs/access-controls/guides/moderated-sessions/#join_sessions
    """

    mode = ast.String("join_session.mode")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


class Session:
    """
    Session is a Teleport session.
    """

    # owner is the session owner
    owner = User("session.owner")

    # participants is a list of session participants
    participants = ast.StringList("session.participants")


class RequestPolicy:
    # names is a list of policy names
    names = ast.StringList("policy.names")

    # approvals is a list of recorded approvals for policy name
    approvals = ast.StringSetMap("policy.approvals")

    # denials is a list of recorded approvals for policy
    denials = ast.StringSetMap("policy.denials")


@scoped
class Request(ast.Predicate):
    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)

    def traverse(self):
        return self.expr.traverse()


@scoped
class Review(ast.Predicate):
    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


class Rules:
    """
    Rules are allow or deny rules.
    """

    def __init__(self, *rules: ast.Predicate):
        self.rules = rules

    def empty(self) -> bool:
        """
        empty returns true if the set of rules is empty.
        """
        return len(self.rules) == 0

    def collect_like(self, other: ast.Predicate):
        """
        collect like returns rules with the same action as the action in `other`.
        TODO: verify that each rule is an action (in `__init__`)
        TODO: verify that `other` is an action
        """
        return [r for r in self.rules if r.__class__ == other.__class__]


# t_expr transforms a predicate-lang expression into a Teleport predicate expression which can be evaluated.
def t_expr(predicate):
    if isinstance(predicate, ast.Predicate):
        return t_expr(predicate.expr)
    elif isinstance(predicate, ast.Eq):
        return f"({t_expr(predicate.L)} == {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Or):
        return f"({t_expr(predicate.L)} || {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.And):
        return f"({t_expr(predicate.L)} && {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Xor):
        return f"({t_expr(predicate.L)} ^ {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Not):
        return f"(!{t_expr(predicate.V)})"
    elif isinstance(predicate, ast.Lt):
        return f"({t_expr(predicate.L)} < {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Le):
        return f"({t_expr(predicate.L)} <= {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Gt):
        return f"({t_expr(predicate.L)} > {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Ge):
        return f"({t_expr(predicate.L)} >= {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.MapIndex):
        return f"{predicate.m.name}[{t_expr(predicate.key)}]"
    elif isinstance(
        predicate,
        (
            ast.String,
            ast.LeqDuration,
            ast.Duration,
            ast.StringList,
            ast.LeqOrderedEnum,
            ast.OrderedEnum,
            ast.Bool,
            ast.Int,
            ast.StringSetMap,
        ),
    ):
        return predicate.name
    elif isinstance(predicate, ast.StringLiteral):
        return f'"{predicate.V}"'
    elif isinstance(predicate, str):
        return f'"{predicate}"'
    elif isinstance(predicate, tuple):
        return f"[{', '.join(t_expr(p) for p in predicate)}]"
    elif isinstance(predicate, (ast.BoolLiteral, ast.IntLiteral, ast.DurationLiteral)):
        return f"{predicate.V}"
    elif isinstance(predicate, ast.Concat):
        return f"({t_expr(predicate.L)} + {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Split):
        return f"split({t_expr(predicate.val)}, {t_expr(predicate.sep)})"
    elif isinstance(predicate, ast.StringTuple):
        return f"[{', '.join(t_expr(p) for p in predicate.vals)}]"
    elif isinstance(predicate, ast.Upper):
        return f"upper({t_expr(predicate.val)})"
    elif isinstance(predicate, ast.Lower):
        return f"lower({t_expr(predicate.val)})"
    elif isinstance(
        predicate,
        (ast.StringListContains, ast.IterableContains, ast.StringSetMapIndexContains),
    ):
        return f"contains({t_expr(predicate.E)}, {t_expr(predicate.V)})"
    elif isinstance(predicate, ast.StringListFirst):
        return f"first({t_expr(predicate.E)})"
    elif isinstance(predicate, (ast.StringListAdd, ast.StringSetMapIndexAdd)):
        return f"add({t_expr(predicate.E)}, {t_expr(predicate.V)})"
    elif isinstance(predicate, (ast.StringListEquals, ast.StringSetMapIndexEquals)):
        return f"equals({t_expr(predicate.E)}, {t_expr(predicate.V)})"
    elif isinstance(
        predicate, (ast.Replace, ast.StringListReplace, ast.StringSetMapIndexReplace)
    ):
        return f"replace({t_expr(predicate.val)}, {t_expr(predicate.src)}, {t_expr(predicate.dst)})"
    elif isinstance(predicate, ast.RegexConstraint):
        return f"regex({t_expr(predicate.expr)})"
    elif isinstance(predicate, ast.RegexTuple):
        return f"[{', '.join(t_expr(p) for p in predicate.vals)}]"
    elif isinstance(predicate, (ast.Matches, ast.IterableMatches)):
        return f"matches({t_expr(predicate.E)}, {t_expr(predicate.V)})"
    elif isinstance(
        predicate, (ast.StringListContainsRegex, ast.StringSetMapIndexContainsRegex)
    ):
        return f"contains_regex({t_expr(predicate.E)}, {t_expr(predicate.V)})"
    elif isinstance(predicate, ast.If):
        return f"if({t_expr(predicate.cond)}, {t_expr(predicate.on_true)}, {t_expr(predicate.on_false)})"
    elif isinstance(predicate, ast.Select):
        return f"select([{', '.join(t_expr(p) for p in predicate.cases)}], {t_expr(predicate.default)})"
    elif isinstance(predicate, ast.Case):
        return f"case({t_expr(predicate.when)}, {t_expr(predicate.then)})"
    elif isinstance(predicate, ast.Default):
        return f"default({t_expr(predicate.expr)})"
    elif isinstance(predicate, ast.StringSetMapIndex):
        return f"{predicate.m.name}[{t_expr(predicate.key)}]"
    elif isinstance(predicate, ast.StringSetMapIndexLen):
        return f"len({t_expr(predicate.E)})"
    elif isinstance(predicate, ast.StringSetMapIndexFirst):
        return f"first({t_expr(predicate.E)})"
    elif isinstance(predicate, ast.StringSetMapAddValue):
        return f"map_add({t_expr(predicate.m.name)}, {t_expr(predicate.K)}, {t_expr(predicate.V)})"
    elif isinstance(predicate, ast.StringSetMapRemoveKeys):
        return f"map_remove({t_expr(predicate.m.name)}, {t_expr(predicate.K)})"
    else:
        raise Exception(f"unknown predicate type: {type(predicate)}")


class Policy:
    def __init__(
        self,
        name: str,
        options: Options = Options(),
        allow: Rules = Rules(),
        deny: Rules = Rules(),
        loud: bool = True,
    ):
        if name == "":
            raise ast.ParameterError("policy name cannot be empty")
        if options.empty() and allow.empty() and deny.empty():
            raise ast.ParameterError(
                "policy must contain either options, allow or deny rules"
            )

        self.name = name
        self.options = options
        self.options.set_defaults()
        self.allow = allow
        self.deny = deny
        self.loud = loud

    def check(self, other: ast.Predicate, other_options: Options = Options()) -> ast.SolverResult:
        return PolicySet([self], self.loud).check(other, other_options)

    def query(self, other: ast.Predicate, other_options: Options = Options()) -> ast.SolverResult:
        return PolicySet([self], self.loud).query(other, other_options)

    def export(self):
        out = {
            "kind": "policy",
            "version": "v1",
            "metadata": {
                "name": self.name,
            },
            "spec": {},
        }

        def group_rules(operator, rules):
            scopes: dict[str, list] = {}
            for rule in rules:
                if rule.scope not in scopes:
                    scopes[rule.scope] = []

                scopes[rule.scope].append(rule)

            for scope, rules in scopes.items():
                expr = functools.reduce(operator, rules)
                scopes[scope] = t_expr(expr)

            return scopes

        if not self.options.empty():
            out["spec"]["options"] = [t_expr(o.expr) for o in self.options.options]

        if not self.allow.empty():
            out["spec"]["allow"] = group_rules(operator.or_, self.allow.rules)

        if not self.deny.empty():
            out["spec"]["deny"] = group_rules(operator.and_, self.deny.rules)

        return out


class PolicySet:
    """
    PolicySet is a set of policies, it merges all allow and all deny rules
    from all other policies.
    """

    def __init__(self, policies: Iterable[Policy], loud: bool = True):
        self.policies = policies
        self.loud = loud

    def build_predicate(self, other: ast.Predicate) -> ast.Predicate:
        """
        build predicate returns a predicate that represents this policy set.

        Allow & deny rules in this policy set with actions different from the action in `other` are filtered out.
        This step is just an optimization so that the final expression sent to Z3 is simpler.
        (Note that we could do something similar for options.)

        Options & rules that were not filtered out are then combined in the following way:
        - options are combined with logical AND
        - allow rules are combined with logical OR
        - deny rules are first negated and then combined with logical AND

        The returned predicate is the logical AND of the 3 above.
        """
        options = []
        allow = []
        deny = []
        for p in self.policies:
            options.extend([o.expr for o in p.options.options])
            allow.extend([e.expr for e in p.allow.collect_like(other)])
            deny.extend([ast.Not(e.expr) for e in p.deny.collect_like(other)])
            
        # as options have defaults, they're always non-empty
        options_expr = functools.reduce(operator.and_, options)

        if allow and deny:
            allow_expr = functools.reduce(operator.or_, allow)
            deny_expr = functools.reduce(operator.and_, deny)
            return ast.Predicate(options_expr & allow_expr & deny_expr, self.loud)
        elif allow:
            allow_expr = functools.reduce(operator.or_, allow)
            return ast.Predicate(options_expr & allow_expr, self.loud)
        elif deny:
            deny_expr = functools.reduce(operator.and_, deny)
            return ast.Predicate(options_expr & deny_expr, self.loud)
        else:
            # TODO: improve error message explaining why
            raise ast.ParameterError("policy set predicate cannot be built")

    def check(self, other: ast.Predicate, other_options: Options = Options()) -> ast.SolverResult:
        return self.build_predicate(other).check(other_options.with_predicate(other), symbols_ignore=lambda s: s.startswith("option."))

    def query(self, other: ast.Predicate, other_options: Options = Options()) -> ast.SolverResult:
        return self.build_predicate(other).query(other_options.with_predicate(other))
