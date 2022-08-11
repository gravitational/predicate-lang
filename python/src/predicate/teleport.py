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
from typing import Final
import functools
import operator
from collections.abc import Iterable

class Node(ast.Predicate):
    '''
    Node is SSH node
    '''
    login = ast.String("node.login")
    labels = ast.StringMap("node.labels")

    def __init__(self, expr):
        ast.Predicate.__init__(self, expr)

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
    def __init__(self, node=None, request: Request = None, review: Review = None):
        self.node = node
        self.request = request
        self.review = review

class Policy:
    def __init__(self, allow: Rules = None, deny: Rules = None):
        if allow is None and deny is None:
            raise ast.ParameterError("provide either allow or deny")
        self.allow = allow or Rules()
        self.deny = deny or Rules()

    def build_predicate(self, other: ast.Predicate):
        # TODO: route the request to the appropriate policy based
        # on the predicate type
        if isinstance(other, Node):
            return predicate(self.allow.node, self.deny.node)
        elif isinstance(other, Request):
            return predicate(self.allow.request, self.deny.request)
        elif isinstance(other, Review):
            return predicate(self.allow.review, self.deny.review)
        raise ast.ParameterError("can't decide how to route query based on the predicate type {}")

    def check(self, other: ast.Predicate):
        return self.build_predicate(other).check(other)

    def query(self, other: ast.Predicate):
        return self.build_predicate(other).query(other)

class PolicySet:
    """
    PolicySet is a set of policies
    """
    def __init__(self, policies: Iterable[Policy]):
        self.policies = policies


def predicate(allow, deny):
    if allow is not None and deny is not None:
        return ast.Predicate(allow.expr & ast.Not(deny.expr))
    if allow is not None:
        return ast.Predicate(allow.expr)
    if deny is not None:
        return ast.Predicate(ast.Not(deny.expr))
