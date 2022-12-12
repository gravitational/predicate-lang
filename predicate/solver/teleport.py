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
import re
from collections.abc import Iterable

import z3

from . import ast
from .errors import ParameterError


def scoped(cls):
    cls.scope = re.sub(r"([a-z])([A-Z])", r"\1_\2", cls.__name__).lower()
    return cls


class SSHOptions:
    """
    SSHOptions defines SSH specific options.
    """

    # The mode used for recording SSH sessions.
    session_recording_mode = ast.StringEnum(
        "options.ssh.session_recording_mode", set([(0, "best_effort"), (1, "strict")])
    )

    # Whether to allow agent forwarding.
    allow_agent_forwarding = ast.Bool("options.ssh.allow_agent_forwarding")

    # Whether to allow port forwarding.
    allow_port_forwarding = ast.Bool("options.ssh.allow_port_forwarding")

    # Whether to allow X11 forwarding.
    allow_x11_forwarding = ast.Bool("options.ssh.allow_x11_forwarding")

    # Whether to allow file copying.
    allow_file_copying = ast.Bool("options.ssh.allow_file_copying")

    # If false, terminates live sessions when the certificate expires.
    allow_expired_cert = ast.Bool("options.ssh.allow_expired_cert")

    # If true, do not enforce IP pinning.
    allow_source_ip_unpinned = ast.Bool("options.ssh.allow_source_ip_unpinned")

    # The max concurrent SSH connections a user can have.
    max_connections = ast.LtInt("options.ssh.max_connections")

    # The max concurrent SSH channels a user can have per connection.
    max_sessions_per_connection = ast.LtInt("options.ssh.max_sessions_per_connection")

    # Disconnect clients after this amount of time of inactivity.
    client_idle_timeout = ast.LtDuration("options.ssh.client_idle_timeout")

class Options(ast.Predicate):
    """
    Options apply to some allow rules if they match
    """

    # SSH specific options
    ssh = SSHOptions

    # Max TTL for issued certificates.
    session_ttl = ast.LtDuration("options.session_ttl")

    # The locking mode used.
    locking_mode = ast.StringEnum(
        "options.locking_mode", set([(0, "best_effort"), (1, "strict")])
    )

    # Enforce per-session MFA or PIV-hardware key restrictions on user login sessions.
    session_mfa = ast.StringEnum("options.session_mfa", set([(0, "no"), (1, "yes")]))

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
class Resource(ast.Predicate):
    """
    Resource defines read/list/write access to a resource.
    """

    # the kind of the resource, such as session_tracker or user
    kind = ast.String("resource.kind")

    # the subkind of the resource
    subkind = ast.String("resource.subkind")

    # the version of the resource
    version = ast.String("resource.version")

    # the name of the resource
    name = ast.String("resource.name")

    # the unique ID of the resource
    id = ast.Int("resource.id")

    # the type of access that is attempted, such as read, write or list
    verb = ast.String("resource.verb")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


@scoped
class AccessNode(ast.Predicate):
    """
    AccessNode defines the permission to access an SSH node.
    """

    login = ast.String("access_node.login")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)
        # TODO check that the predicate is complete, has listed logins

    def __and__(self, options: Options):
        """
        This is a somewhat special case, options define max session TTL,
        so this operator constructs a node predicate that contains options
        that are relevant to node.
        """
        return AccessNode(self.expr & options.expr)


class Node:
    """
    Node is an SSH node.
    """

    # hostname of the node
    hostname = ast.String("node.hostname")

    # uuid of the node
    uuid = ast.String("node.uuid")

    # address is the public address reported by the node
    address = ast.String("node.address")

    # labels are the node labels
    labels = ast.StringMap("node.labels")


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

    # policies is a list of access policies assigned to the user
    polices = ast.StringList("user.policies")

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
    Rules are allow or deny rules
    """

    def __init__(self, *rules):
        self.rules = rules or []

    def collect_like(self, other: ast.Predicate):
        return [r for r in self.rules if r.__class__ == other.__class__]

optionsPrefix = "options."

# option_optimize optimizes the option literal towards it's preferred value.
def option_optimize(optimizer, literal):
    match literal.name:
        case Options.session_ttl.name:
            return optimizer.maximize(literal.val)
        case _:
            raise Exception("failed to optimize unknown option")

# point_evaluate options evaluates options set and returns a map of options values suitable for export.
def point_evaluate_options(set: OptionsSet):
    options = {}

    for option_clause in set.options:
        literal = option_search_unknown(option_clause.expr)
        if literal is None:
            raise ParameterError("unknown option not found")

        optimizer = z3.Optimize()
        optimizer.add(option_clause.expr.traverse())
        option_optimize(optimizer, literal)
        if optimizer.check() == z3.unsat:
            raise ParameterError("our own predicate is unsolvable")

        export_name = literal.name[len(optionsPrefix):]
        options[export_name] = optimizer.model()[literal.val].__str__()

    return options

# option_search_unknown searches for unknown option identifiers in the predicate.
def option_search_unknown(predicate):
    if isinstance(predicate, (ast.StringEnum,ast.Bool,ast.LtInt,ast.LtDuration)):
        if not predicate.name.startswith(optionsPrefix):
            return None

        return predicate
    elif isinstance(predicate, (ast.And, ast.Or,ast.Eq,ast.Lt)):
        return option_search_unknown(predicate.L) or option_search_unknown(predicate.R)
    elif isinstance(predicate, ast.Not):
        return option_search_unknown(predicate.expr)
    else:
        return None


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
        return f"xor({t_expr(predicate.L)}, {t_expr(predicate.R)})"
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
            ast.LtDuration,
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
        return f"array({', '.join(t_expr(p) for p in predicate)})"
    elif isinstance(predicate, (ast.BoolLiteral, ast.IntLiteral, ast.DurationLiteral)):
        return f"{predicate.V}"
    elif isinstance(predicate, ast.Concat):
        return f"({t_expr(predicate.L)} + {t_expr(predicate.R)})"
    elif isinstance(predicate, ast.Split):
        return f"split({t_expr(predicate.val)}, {t_expr(predicate.sep)})"
    elif isinstance(predicate, ast.StringTuple):
        return f"array({', '.join(t_expr(p) for p in predicate.vals)})"
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
        return f"append({t_expr(predicate.E)}, {t_expr(predicate.V)})"
    elif isinstance(predicate, (ast.StringListEquals, ast.StringSetMapIndexEquals)):
        return f"({t_expr(predicate.E)} == {t_expr(predicate.V)})"
    elif isinstance(
        predicate, (ast.Replace, ast.StringListReplace, ast.StringSetMapIndexReplace)
    ):
        return f"replace({t_expr(predicate.val)}, {t_expr(predicate.src)}, {t_expr(predicate.dst)})"
    elif isinstance(predicate, ast.RegexConstraint):
        return f"regex({t_expr(predicate.expr)})"
    elif isinstance(predicate, ast.RegexTuple):
        return f"array({', '.join(t_expr(p) for p in predicate.vals)})"
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
        return f"map_insert({t_expr(predicate.m.name)}, {t_expr(predicate.K)}, {t_expr(predicate.V)})"
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

    def check(self, other: ast.Predicate):
        return PolicySet([self], self.loud).check(other)

    def query(self, other: ast.Predicate):
        return PolicySet([self], self.loud).query(other)

    def build_predicate(self, other: ast.Predicate):
        return PolicySet([self], self.loud).build_predicate(other)

    def export(self):
        out = {
            "kind": "access_policy",
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

        if self.allow.rules:
            out["spec"]["allow"] = group_rules(operator.or_, self.allow.rules)

        if self.deny.rules:
            out["spec"]["deny"] = group_rules(operator.and_, self.deny.rules)

        if self.options:
            out["spec"]["options"] = point_evaluate_options(self.options)

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
