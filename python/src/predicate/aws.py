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

## NOTE
## Convert AWS policies to predictate expression.
# It's not that the policy that should be modeled,
# it's the action against resource that should be modeled,
# AWS policy should be converted to predicate.
# Because it's not AWS policy that should be introspected, but action.
# AWS policy is meta?

class Action:
    resource = ast.String('action.resource')
    action = ast.String('action.action')


def statement(p: dict):
    ## TODO: convert this policy to Predicate expression
    allow = False
    if p["Effect"] == "Allow":
        allow = True
    elif p["Effect"] == "Deny":
        allow = False
    else:
        raise ParameterError("unsupported effect", p["Effect"])
    
    resources = p["Resource"]
    if isinstance(resources, str):
        resources = [resources]
    actions = p["Action"]
    if isinstance(actions, str):
        actions = [actions]

    expr = (regex.tuple(_to_regex(r) for r in resources).matches(Action.resource)
        &
        regex.tuple(_to_regex(a) for a in actions).matches(Action.action))
    if not allow:
        expr = ast.Not(expr)

    return ast.Predicate(expr)


def _to_regex(v: str):
    if v.endswith("*"):
        v = v.rstrip("*")
        if "*" in v:
            raise ast.ParameterError("can only end with wildcard")
        return v + ".*"
    if "*" in v:
        raise ast.ParameterError("can only end with wildcard")
    return v
    
