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

import z3

from . import ast
from .errors import ParameterError


def scoped(cls):
    cls.scope = cls.__name__.lower()
    return cls


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


@scoped
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
    ret, model = p.check(ast.Predicate(traits_expr))
    if not ret:
        return ()
    out = []

    def first(depth):
        vals = policy_map_expr.traverse()
        for i in range(depth):
            vals = ast.StringListSort.cdr(vals)
        expr = ast.fn_string_list_first(vals)
        return model.eval(expr).as_string()

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
    User is a Teleport user
    """

    # name is username
    name = ast.String("user.name")

    # traits is a map of user traits
    traits = ast.StringSetMap("user.traits")


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
    Rules are allow or deny rules
    """

    def __init__(self, *rules):
        self.rules = rules or []

    def collect_like(self, other: ast.Predicate):
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
    elif isinstance(predicate, ast.Gt):
        return f"({t_expr(predicate.L)} > {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.MapIndex):
        return f"{predicate.m.name}[{t_expr(predicate.key)}]"
    elif isinstance(
        predicate,
        (
            ast.String,
            ast.Duration,
            ast.StringList,
            ast.StringEnum,
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
        options: OptionsSet = None,
        allow: Rules = None,
        deny: Rules = None,
        loud: bool = True,
    ):
        self.name = name
        if name == "":
            raise ast.ParameterError("supply a valid name")
        if allow is None and deny is None:
            raise ast.ParameterError("provide either allow or deny")
        self.allow = allow or Rules()
        self.deny = deny or Rules()
        self.options = options or OptionsSet()
        self.loud = loud

    def symbols(self) -> set[str]:
        """
        symbols returns all predicate symbols present in the policy.
        """
        return PolicySet([self], self.loud).symbols()

    def check(self, other: ast.Predicate):
        return PolicySet([self], self.loud).check(other)

    def query(self, other: ast.Predicate):
        return PolicySet([self], self.loud).query(other)

    def build_predicate(self, other: ast.Predicate) -> ast.Predicate:
        return PolicySet([self], self.loud).build_predicate(other)

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
            scopes = {}
            for rule in rules:
                if rule.scope not in scopes:
                    scopes[rule.scope] = []

                scopes[rule.scope].append(rule)

            for scope, rules in scopes.items():
                expr = functools.reduce(operator, rules)
                scopes[scope] = t_expr(expr)

            return scopes

        if self.options.options:
            options_rules = functools.reduce(operator.and_, self.options.options)
            out["spec"]["options"] = t_expr(options_rules)

        if self.allow.rules:
            out["spec"]["allow"] = group_rules(operator.or_, self.allow.rules)

        if self.deny.rules:
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
        # if option predicates are present, apply them as mandatory
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
            pr = ast.Predicate(allow_expr, self.loud)
        elif not allow_expr:
            pr = ast.Predicate(deny_expr, self.loud)
        else:
            pr = ast.Predicate(allow_expr & deny_expr, self.loud)
        return pr

    def symbols(self) -> set[str]:
        """
        symbols returns all predicate symbols present in the policy set.
        """
        symbols = set()
        for p in self.policies:
            for e in p.options.options:
                symbols = symbols.union(e.symbols)
            for e in p.allow.rules:
                symbols = symbols.union(e.symbols)
            for e in p.deny.rules:
                symbols = symbols.union(e.symbols)
        return symbols

    def check(self, other: ast.Predicate):
        return self.build_predicate(other).check(other)

    def query(self, other: ast.Predicate):
        return self.build_predicate(other).query(other)

    def names(self) -> set[str]:
        """
        Names returns names in the policy set
        """
        s = set()
        for p in self.policies:
            s.add(p.name)
        return s

class TeleportNode:
    """
    TeleportNode contains information about a teleport node (hostname & labels).
    """

    def __init__(self, hostname, labels={}):
        self.hostname = hostname
        self.labels = labels

    def __repr__(self):
        return "TeleportNode(hostname = {}, labels = {})".format(self.hostname, self.labels)

    def parse(node):
        """
        parse extracts the hostname & labels of a node from the JSON output of `tctl get nodes`.
        Note that both `labels` & `cmd_labels` are considered as labels.
        """
        hostname = node["spec"]["hostname"]
        labels = {}
        if "labels" in node["metadata"]:
            for key, value in node["metadata"]["labels"].items():
                labels[key] = value
        if "cmd_labels" in node["spec"]:
            for key, value in node["spec"]["cmd_labels"].items():
                labels[key] = value["result"]

        return TeleportNode(hostname, labels)

    def predicate(self, policy: Policy) -> ast.Predicate:
        """
        predicate builds a predicate representing this node.
        The predicate returned only contains symbols present in the policy passed as argument
        (which ensures that the predicate returned can be used to query to policy).
        TODO it's unclear why the query symbols have to be a subset of the policy/predicate symbols.
        """
        symbols = policy.symbols()
        predicate = ast.BoolLiteral(True)
        for key, value in self.labels.items():
            if ast.symbol(Node.labels[key]) in symbols:
                predicate = predicate & (Node.labels[key] == value)
        return predicate

class TeleportUser:
    """
    TeleportUser contains information about a teleport user (name & traits).
    """

    def __init__(self, name, traits={}):
        self.name = name
        self.traits = traits

    def __repr__(self):
        return "TeleportUser(name = {}, traits = {})".format(self.name, self.traits)

    def parse(user):
        """
        parse extracts the name & traits of a user from the JSON output of `tctl get users`.
        """
        name = user["metadata"]["name"]
        traits = {}
        if "traits" in user["spec"]:
            for key, values in user["spec"]["traits"].items():
                if values != None:
                    traits[key] = values

        return TeleportUser(name, traits)

    def predicate(self, policy: Policy) -> ast.Predicate:
        """
        predicate builds a predicate representing this user.
        The predicate returned only contains symbols present in the policy passed as argument
        (which ensures that the predicate returned can be used to query to policy).
        TODO it's unclear why the query symbols have to be a subset of the policy/predicate symbols.
        """
        symbols = policy.symbols()
        predicate = ast.BoolLiteral(True)

        if ast.symbol(User.name) in symbols:
            predicate = predicate & (User.name == self.name)

        for key, values in self.traits.items():
            if ast.symbol(User.traits[key]) in symbols:
                predicate = predicate & (User.traits[key] == values)

        return predicate

    def logins(self, node: TeleportNode, policy: Policy, loud=False, max=3):
        """
        logins returns a list of valid logins that this user can use to access
        the `node` (passed as argument) given the `policy` (passed as argument).

        As the list of valid logins may be infinite, the `max` argument
        is used to limit the size of the list returned.

        If the list returned is empty, then the user cannot access the node.
        """
        logins = []
        predicate = self.predicate(policy) & node.predicate(policy)

        # compute the set of symbols that are mentioned in the policy, but are not
        # mentioned by the user & node predicate.
        # `user.name`` is always present (as this is a required field), so the missing
        # symbols can only be of the following form:
        # - `user.traits.*`
        # - `node.labels.*`
        missing_symbols = policy.symbols().difference(Node(predicate).symbols)

        # for any such symbol, set it to some reserved value.
        # TODO explain why
        for symbol in missing_symbols:
            if symbol.startswith("user.traits."):
                key = symbol.removeprefix("user.traits.")
                predicate = predicate & (User.traits[key] == ("$RESERVED_VALUE$",))
            elif symbol.startswith("node.labels."):
                key = symbol.removeprefix("node.labels.")
                predicate = predicate & (Node.labels[key] == "$RESERVED_VALUE$")

        while len(logins) < max:
            # the base query is the predicate that represents both the user & the node.
            # this base query is extended so that z3 only returns logins that haven't
            # been returned by previous queries.
            query = predicate
            for login in logins:
                query = query & (Node.login != login)

            if loud:
                print("query  = {}".format(query))

            solves, result = policy.query(Node(query))
            if solves & loud:
                print("solves = {}".format(solves))
                print("model  = ")
                show_teleport_model(result)

            if solves:
                # if the query is solvable, then we extract the login from the model.
                login = result[Node.login.val]
                if login != None:
                    logins.append(login.as_string())
                else:
                    # if the policy set doesn't say anything about the login, then it
                    # won't be part of the model.
                    # when this happens, we just make up a list of logins.
                    return ["login{}".format(i) for i in range(max)]

            else:
                if loud:
                    print(result)
                break

        return logins

def show_teleport_model(model):
    for d in model.decls():
        if d.name().startswith("node.") or d.name().startswith("user."):
            print("    {}: {}".format(d.name(), model[d]))
