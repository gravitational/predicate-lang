'''
Copyright 2022 Gravitational, Inc, Andrew Helwer

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
from . import ast
from dataclasses import dataclass
from collections.abc import Iterable

class Matches:
    def __init__(self, expr, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return '''({}.matches({}))'''.format(self.E, self.V)

    def traverse(self):
        return z3.InRe(self.V.traverse(), self.E.traverse())

    def __or__(self, other):
        return ast.Or(self, other)

    def __xor__(self, other):
        return ast.Xor(self, other)    

    def __and__(self, other):
        return ast.And(self, other)

    def __invert__(self):
        return ast.Not(self)

class RegexConstraint:

    def __init__(self, expr: str):
        parsed_regex = sre_parse.parse(expr)
        is_regex = any(
            [sre_constants.LITERAL != node_type for node_type, _ in parsed_regex.data]
        )
        if is_regex is None:
            raise ParameterError("{} is not a valid regex")
        self.regex = parsed_regex
        self.expr = expr

    def matches(self, other):
        return Matches(self, other)

    def traverse(self):
        return regex_to_z3_expr(self.regex)

    def walk(self, fn):
        fn(self)
        fn(self.regex)

    def __str__(self):
        return 'regex(`{}`)'.format(self.expr)


class IterableMatches:
    def __init__(self, expr: Iterable, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return '''({}.matches({}))'''.format(self.E, self.V)

    def traverse(self):
        return z3.Or(*[
            Matches(e, self.V).traverse()
            for e in self.E.vals
        ])

    def __or__(self, other):
        return ast.Or(self, other)

    def __xor__(self, other):
        return ast.Xor(self, other)    

    def __and__(self, other):
        return ast.And(self, other)

    def __invert__(self):
        return ast.Not(self)

@dataclass
class RegexTuple:
    vals: Iterable[RegexConstraint]

    def matches(self, val):
        if isinstance(val, str):
            return IterableMatches(self, ast.StringLiteral(val))
        if isinstance(val, ast.String):
            return IterableMatches(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def walk(self, fn):
        fn(self)
        fn(self.vals)

    def __str__(self):
        return '[{}]'.format(", ".join(['`{}`'.format(v) for v in self.vals]))

def parse(value: str):
    """
    Attempts to parse the given value as a regex.
    """
    return RegexConstraint(value)

def tuple(values: Iterable[str]):
    """
    Attempts to parse the given iterable as iterable of regular expression.
    """
    return RegexTuple([parse(v) for v in values])

def regex_to_z3_expr(regex: sre_parse.SubPattern) -> z3.ReRef:
    """
    Translates a parsed regex into its Z3 equivalent.
    The parsed regex is a sequence of regex constructs (literals, *, +, etc.)
    """
    if 0 == len(regex.data):
        raise ValueError("ERROR: regex is empty")
    elif 1 == len(regex.data):
        return regex_construct_to_z3_expr(regex.data[0])
    else:
        return z3.Concat(
            [regex_construct_to_z3_expr(construct) for construct in regex.data]
        )


def regex_construct_to_z3_expr(regex_construct) -> z3.ReRef:
    """
    Translates a specific regex construct into its Z3 equivalent.
    """
    node_type, node_value = regex_construct
    if sre_constants.LITERAL == node_type:  # a
        return z3.Re(chr(node_value))
    if sre_constants.NOT_LITERAL == node_type:  # [^a]
        return Minus(AnyChar(), z3.Re(chr(node_value)))
    if sre_constants.SUBPATTERN == node_type:
        _, _, _, value = node_value
        return regex_to_z3_expr(value)
    elif sre_constants.ANY == node_type:  # .
        return AnyChar()
    elif sre_constants.MAX_REPEAT == node_type:
        low, high, value = node_value
        if (0, 1) == (low, high):  # a?
            return z3.Option(regex_to_z3_expr(value))
        elif (0, sre_constants.MAXREPEAT) == (low, high):  # a*
            return z3.Star(regex_to_z3_expr(value))
        elif (1, sre_constants.MAXREPEAT) == (low, high):  # a+
            return z3.Plus(regex_to_z3_expr(value))
        else:  # a{3,5}, a{3}
            return z3.Loop(regex_to_z3_expr(value), low, high)
    elif sre_constants.IN == node_type:  # [abc]
        first_subnode_type, _ = node_value[0]
        if sre_constants.NEGATE == first_subnode_type:  # [^abc]
            return Minus(
                AnyChar(),
                z3.Union(
                    [regex_construct_to_z3_expr(value) for value in node_value[1:]]
                ),
            )
        else:
            return z3.Union([regex_construct_to_z3_expr(value) for value in node_value])
    elif sre_constants.BRANCH == node_type:  # ab|cd
        _, value = node_value
        return z3.Union([regex_to_z3_expr(v) for v in value])
    elif sre_constants.RANGE == node_type:  # [a-z]
        low, high = node_value
        return z3.Range(chr(low), chr(high))
    elif sre_constants.CATEGORY == node_type:  # \d, \s, \w
        if sre_constants.CATEGORY_DIGIT == node_value:  # \d
            return category_regex(node_value)
        elif sre_constants.CATEGORY_NOT_DIGIT == node_value:  # \D
            return Minus(AnyChar(), category_regex(sre_constants.CATEGORY_DIGIT))
        elif sre_constants.CATEGORY_SPACE == node_value:  # \s
            return category_regex(node_value)
        elif sre_constants.CATEGORY_NOT_SPACE == node_value:  # \S
            return Minus(AnyChar(), category_regex(sre_constants.CATEGORY_SPACE))
        elif sre_constants.CATEGORY_WORD == node_value:  # \w
            return category_regex(node_value)
        elif sre_constants.CATEGORY_NOT_WORD == node_value:  # \W
            return Minus(AnyChar(), category_regex(sre_constants.CATEGORY_WORD))
        else:
            raise NotImplementedError(
                f"ERROR: regex category {node_value} not implemented"
            )
    elif sre_constants.AT == node_type:
        if node_value in {
            sre_constants.AT_BEGINNING,
            sre_constants.AT_BEGINNING_STRING,
        }:  # ^a, \A
            raise NotImplementedError(
                f"ERROR: regex position {node_value} not implemented"
            )
        elif sre_constants.AT_BOUNDARY == node_value:  # \b
            raise NotImplementedError(
                f"ERROR: regex position {node_value} not implemented"
            )
        elif sre_constants.AT_NON_BOUNDARY == node_value:  # \B
            raise NotImplementedError(
                f"ERROR: regex position {node_value} not implemented"
            )
        elif node_value in {
            sre_constants.AT_END,
            sre_constants.AT_END_STRING,
        }:  # a$, \Z
            raise NotImplementedError(
                f"ERROR: regex position {node_value} not implemented"
            )
        else:
            raise NotImplementedError(
                f"ERROR: regex position {node_value} not implemented"
            )
    else:
        raise NotImplementedError(
            f"ERROR: regex construct {regex_construct} not implemented"
        )

def Minus(re1: z3.ReRef, re2: z3.ReRef) -> z3.ReRef:
    """
    The Z3 regex matching all strings accepted by re1 but not re2.
    Formatted in camelcase to mimic Z3 regex API.
    """
    return z3.Intersect(re1, z3.Complement(re2))


def AnyChar() -> z3.ReRef:
    """
    The Z3 regex matching any character (currently only ASCII supported).
    Formatted in camelcase to mimic Z3 regex API.
    """
    return z3.Range(chr(0), chr(127))    
