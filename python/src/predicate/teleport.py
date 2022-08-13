'''
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
'''

import z3
import re
import sre_constants
import sre_parse
from .errors import ParameterError
from . import ast, regex
from dataclasses import dataclass
from collections.abc import Iterable
import functools
import operator
from collections.abc import Iterable

class Options(ast.Predicate):
    '''
    Options apply to some allow rules if they match
    '''
    max_session_ttl = ast.Duration("options.max_session_ttl")

    pin_source_ip = ast.Bool("options.pin_source_ip")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)


class Node(ast.Predicate):
    '''
    Node is SSH node
    '''
    login = ast.String("node.login")
    labels = ast.StringMap("node.labels")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)
        # TODO check that the predicate is complete, has listed logins

    def __and__(self, options: Options):
        '''
        This is a somewhat special case, options define max session TTL,
        so this operator constructs a node predicate that contains options
        that are relevant to node.
        '''
        return Node(self.expr & options.expr)

class User:
    '''
    User is a Teleport user
    '''
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
    '''
    Rules are allow or deny rules
    '''
    def __init__(self, node: Node=None, request: Request = None, review: Review = None):
        self.node = node
        self.request = request
        self.review = review

class Policy:
    def __init__(self, options: Options = None, allow: Rules = None, deny: Rules = None):
        if allow is None and deny is None:
            raise ast.ParameterError("provide either allow or deny")
        self.allow = allow or Rules()
        self.deny = deny or Rules()
        self.options = options

    def build_predicate(self, other: ast.Predicate):
        def predicate(allow, deny, options = None):
            expr = None
            if allow is not None and deny is not None:
                if options is not None:
                    return ast.Predicate(options.expr & allow.expr & ast.Not(deny.expr))
                return ast.Predicate(allow.expr & ast.Not(deny.expr))
            if allow is not None:
                if options is not None:                
                    return ast.Predicate(options.expr & allow.expr)
                return ast.Predicate(allow.expr)
            if deny is not None:
                return ast.Predicate(ast.Not(deny.expr))
        # TODO: route the request to the appropriate policy based
        # on the predicate type
        if isinstance(other, Node):
            return predicate(self.allow.node, self.deny.node, self.options)
        elif isinstance(other, Request):
            return predicate(self.allow.request, self.deny.request)
        elif isinstance(other, Review):
            return predicate(self.allow.review, self.deny.review)
        raise ast.ParameterError("can't decide how to route query based on the predicate type {}")

    def check(self, other: ast.Predicate):
        return self.build_predicate(other).check(other)

    def query(self, other: ast.Predicate):
        return self.build_predicate(other).query(other)

class PolicySet(Policy):
    """
    PolicySet is a set of policies, it merges all allow and all deny rules
    from all other policies.
    """
    def __init__(self, policies: Iterable[Policy]):
        self.policies = policies


    def build_predicate(self, other: ast.Predicate):
        # TODO: route the request to the appropriate policy based
        # on the predicate type
        def collect_predicates(policies, get_allow, get_deny):
            allow = []
            deny = []
            for p in policies:
                pr = get_allow(p)
                if pr:
                    allow.append(pr.expr)
                pr = get_deny(p)
                if pr:
                    deny.append(ast.Not(pr.expr))
            return allow, deny

        if isinstance(other, Node):
            allow, deny = collect_predicates(self.policies,
                                             lambda rule: rule.allow.node,
                                             lambda rule: rule.deny.node)
        elif isinstance(other, Request):
            allow, deny = collect_expressions(self.policies,
                                              lambda rule: rule.allow.request,
                                              lambda rule: rule.deny.request)
        elif isinstance(other, Review):
            allow, deny = collect_expressions(self.policies,
                                              lambda rule: rule.allow.review,
                                              lambda rule: rule.deny.review)
        else:
            raise ast.ParameterError("can't decide how to route query based on the predicate type {}")
        if not allow and not deny:
            raise ast.ParameterError("policy set is empty {}")
        if not deny:
            return ast.Predicate(functools.reduce(operator.or_, allow))
        if not allow:
            return ast.Predicate(functools.reduce(operator.and_, deny))
        return ast.Predicate(functools.reduce(operator.or_, allow) & functools.reduce(operator.and_, deny))

    def check(self, other: ast.Predicate):
        return self.build_predicate(other).check(other)

    def query(self, other: ast.Predicate):
        return self.build_predicate(other).query(other)        

