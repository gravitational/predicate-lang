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

class Node:
    '''
    Node is SSH node
    '''
    label = ast.String("node.label")
    login = ast.String("node.login")

class User:
    '''
    User is a Teleport user
    '''
    # name is username
    name = ast.String("user.name")

    # trait is a user trait
    trait = ast.String("user.trait")


def verify_expression(s, expr):
    '''
    '''
    
    if type(expr) == String:
        s.add(expr.name)

        
class Rules:
    def __init__(self, expr):
        expr.walk(verify_expression)
        self.expr = expr
        self.expr.walk

class Policy:
    def __init__(self, allow: Rules):
        self.allow = allow


