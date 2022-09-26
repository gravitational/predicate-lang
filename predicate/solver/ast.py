"""
Copyright 2022 Gravitational, Inc, Andrew Helwer, Alexander Klizhentas

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

# Z3 programming
#
# * tutorial https://ericpony.github.io/z3py-tutorial/guide-examples.htm
# * book https://theory.stanford.edu/~nikolaj/programmingz3.html
# * reference https://z3prover.github.io/api/html/namespacez3py.html

import functools
import operator
import sre_constants
import sre_parse
import typing
from collections.abc import Iterable
from dataclasses import dataclass

import z3

from .errors import ParameterError


class LogicMixin:
    """
    LogicMixin contains usual &, |, ^ and ! operators
    used in any boolean logic expression
    """

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)


class Matches(LogicMixin):
    def __init__(self, expr, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.matches({}))""".format(self.E, self.V)

    def traverse(self):
        return z3.InRe(self.V.traverse(), self.E.traverse())


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
        return "regex(`{}`)".format(self.expr)


class IterableMatches(LogicMixin):
    def __init__(self, expr: Iterable, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.matches({}))""".format(self.E, self.V)

    def traverse(self):
        return z3.Or(*[Matches(e, self.V).traverse() for e in self.E.vals])


@dataclass
class RegexTuple:
    vals: Iterable[RegexConstraint]

    def matches(self, val):
        if isinstance(val, str):
            return IterableMatches(self, StringLiteral(val))
        if isinstance(val, String):
            return IterableMatches(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def walk(self, fn):
        fn(self)
        fn(self.vals)

    def __str__(self):
        return "[{}]".format(", ".join(["`{}`".format(v) for v in self.vals]))


def parse_regex(value: str):
    """
    Attempts to parse the given value as a regex.
    """
    return RegexConstraint(value)


def regex_tuple(values: Iterable[str]):
    """
    Attempts to parse the given iterable as iterable of regular expression.
    """
    return RegexTuple([parse_regex(v) for v in values])


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


def category_regex(category: sre_constants._NamedIntConstant) -> z3.ReRef:
    """
    Defines regex categories in Z3.
    """
    if sre_constants.CATEGORY_DIGIT == category:
        return z3.Range("0", "9")
    elif sre_constants.CATEGORY_SPACE == category:
        return z3.Union(
            z3.Re(" "), z3.Re("\t"), z3.Re("\n"), z3.Re("\r"), z3.Re("\f"), z3.Re("\v")
        )
    elif sre_constants.CATEGORY_WORD == category:
        return z3.Union(
            z3.Range("a", "z"), z3.Range("A", "Z"), z3.Range("0", "9"), z3.Re("_")
        )
    else:
        raise NotImplementedError(
            f"ERROR: regex category {category} not yet implemented"
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


class StringLiteral:
    """
    StringLiteral represents a string value - e.g. StringLiteral('potato')
    """

    def __init__(self, val: str):
        self.V = val

    def traverse(self):
        return z3.StringVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return "`{}`".format(self.V)


class IntLiteral:
    """
    IntLiteral is integer value, e.g. IntLiteral(7)
    """

    def __init__(self, val: int):
        self.V = val

    def traverse(self):
        return z3.IntVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return "`{}`".format(self.V)


NANOSECOND = 1
MICROSECOND = 1000 * NANOSECOND
MILLISECOND = 1000 * MICROSECOND
SECOND = 1000 * MILLISECOND
MINUTE = 60 * SECOND
HOUR = 60 * MINUTE


class DurationLiteral:
    """
    Duration literal measures time in nanoseconds
    """

    def __init__(self, val: int):
        self.V = val

    def traverse(self):
        return z3.IntVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return "`{}`".format(self.V)


class BoolLiteral:
    """
    Boolean literal is true or false
    """

    def __init__(self, val: bool):
        self.V = val

    def traverse(self):
        return z3.BoolVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return "`{}`".format(self.V)


class Int:
    """
    Int is integer variable, e.g. count = Int('count')
    """

    def __init__(self, name: str):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.IntSort())

    def __eq__(self, val):
        if isinstance(val, int):
            return Eq(self, IntLiteral(val))
        if isinstance(val, (Int,)):
            return Eq(self, val)
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __ne__(self, val):
        if isinstance(val, int):
            return Not(Eq(self, IntLiteral(val)))
        if isinstance(val, (Int,)):
            return Not(Eq(self, val))
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __lt__(self, val):
        if isinstance(val, int):
            return Lt(self, IntLiteral(val))
        if isinstance(val, (Int,)):
            return Lt(self, val)
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __gt__(self, val):
        if isinstance(val, int):
            return Gt(self, IntLiteral(val))
        if isinstance(val, (Int,)):
            return Gt(self, val)
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)

    def __str__(self):
        return "int({})".format(self.name)


class Duration:
    def __init__(self, name: str):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.IntSort())

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)

    def __str__(self):
        return "duration({})".format(self.name)

    @staticmethod
    def new(
        hours: int = 0,
        minutes: int = 0,
        seconds: int = 0,
        milliseconds: int = 0,
        microseconds: int = 0,
        nanoseconds: int = 0,
    ) -> DurationLiteral:
        return DurationLiteral(
            hours * HOUR
            + minutes * MINUTE
            + seconds * SECOND
            + milliseconds * MILLISECOND
            + microseconds * MICROSECOND
            + nanoseconds * NANOSECOND
        )

    def __eq__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Eq(self, val)
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __ne__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Not(Eq(self, val))
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __lt__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Lt(self, val)
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __gt__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Gt(self, val)
        raise TypeError(
            "unsupported type {}, supported duration and duration literals only".format(
                type(val)
            )
        )


class Bool:
    def __init__(self, name: str):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.BoolSort())

    def __eq__(self, val):
        if isinstance(val, bool):
            return Eq(self, BoolLiteral(val))
        if isinstance(val, (Bool,)):
            return Eq(self, val)
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def __ne__(self, val):
        if isinstance(val, bool):
            return Not(Eq(self, BoolLiteral(val)))
        if isinstance(val, (Bool,)):
            return Not(Eq(self, val))
        raise TypeError(
            "unsupported type {}, supported integers only".format(type(val))
        )

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)

    def __str__(self):
        return "bool({})".format(self.name)


class String:
    def __init__(self, name: str):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.StringSort())

    def __eq__(self, val):
        if isinstance(val, str):
            return Eq(self, StringLiteral(val))
        if isinstance(
            val, (String, Concat, Split, Replace, StringSetMapIndexFirst, Upper, Lower)
        ):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, str):
            return Not(Eq(self, StringLiteral(val)))
        if isinstance(
            val, (String, Concat, Split, Replace, StringSetMapIndexFirst, Upper, Lower)
        ):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __add__(self, val):
        if isinstance(val, str):
            return Concat(self, StringLiteral(val))
        if isinstance(
            val, (String, Concat, Split, Replace, StringSetMapIndexFirst, Upper, Lower)
        ):
            return Concat(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __radd__(self, val):
        if isinstance(val, str):
            return Concat(StringLiteral(val), self)
        if isinstance(
            val, (String, Concat, Split, Replace, StringSetMapIndexFirst, Upper, Lower)
        ):
            return Concat(val, self)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def upper(self):
        return Upper(self)

    def lower(self):
        return Lower(self)

    def before_delimiter(self, sep: str):
        """ """
        return Split(self, StringLiteral(sep), before=True)

    def after_delimiter(self, sep: str):
        """ """
        return Split(self, StringLiteral(sep), before=False)

    def replace(self, src: str, dst: str):
        """ """
        return Replace(self, StringLiteral(src), StringLiteral(dst))

    def __str__(self):
        return "string({})".format(self.name)

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)


def define_enum_fn(fn_map, fn_key, kv: typing.Dict[String, Int]):
    """
    Define mapfn defines a key value map using recursive Z3 function,
    essentially converting {'a': 1} into if x == 'a' then 1 else ...
    """

    def iff(iterator):
        try:
            key, val = next(iterator)
        except StopIteration:
            return z3.IntVal(-1)
        else:
            return z3.If(fn_key == z3.StringVal(key), z3.IntVal(val), iff(iterator))

    z3.RecAddDefinition(fn_map, [fn_key], iff(iter(kv.items())))


class StringEnum:
    def __init__(self, name, values):
        def transform_values():
            out = {}
            for (i, v) in enumerate(values):
                if isinstance(v, str):
                    out[v] = i
                elif isinstance(v, tuple) and list(map(type, v)) == [int, str]:
                    out[v[1]] = v[0]
                else:
                    raise ParameterError("unsupported enum value: {}".format(v))
            return out

        self.values: typing.Dict[String, Int] = transform_values()
        self.name = name
        self.fn = z3.RecFunction(self.name, z3.StringSort(), z3.IntSort())
        self.fn_key = z3.RecFunction(
            self.name + "_keys", z3.StringSort(), z3.BoolSort()
        )
        self.fn_key_arg = z3.String(self.name + "_key_arg")

        required_key = z3.String(self.name + "_required_key")
        z3.RecAddDefinition(
            self.fn_key,
            [required_key],
            z3.BoolVal(False)
            if len(values) == 0
            else z3.Or([required_key == z3.StringVal(key) for key in self.values]),
        )
        define_enum_fn(self.fn, z3.String(self.name + "_arg"), self.values)

    def one_of(self):
        return functools.reduce(operator.or_, [self == key for key in self.values])

    def __eq__(self, val):
        if isinstance(val, str):
            return Eq(self, StringLiteral(val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, str):
            return Not(Eq(self, StringLiteral(val)))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __lt__(self, val):
        if isinstance(val, str):
            if val not in self.values:
                raise ParameterError(
                    "value {} is not a valid enum, valid are: {}".format(
                        val, [v for v in self.values]
                    )
                )
            return Lt(self, StringLiteral(val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __gt__(self, val):
        if isinstance(val, str):
            return Gt(self, StringLiteral(val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __str__(self):
        return "enum({})".format(self.name)

    def compare(self, op, other):
        # we always convert enum to the following function call spec:
        #
        # enum("apple") = 1
        # enum("banana") = 2
        #
        # This converts expression
        # enum > "apple"
        #
        # to
        #
        # enum(x) > enum("apple") & enum_key["apple"] == True
        #
        # where x is just a free variable associated with the function
        #
        return z3.And(
            op(self.fn(self.fn_key_arg), self.fn(other)),
            self.fn_key(other) == z3.BoolVal(True),
        )

    def walk(self, fn):
        fn(self)


class IterableContains(LogicMixin):
    def __init__(self, expr: Iterable, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.contains({}))""".format(self.E, self.V)

    def traverse(self):
        return z3.Or(
            *[StringLiteral(v).traverse() == self.V.traverse() for v in self.E.vals]
        )


@dataclass
class StringTuple:
    vals: Iterable[str]

    def contains(self, val):
        if isinstance(val, str):
            return IterableContains(self, StringLiteral(val))
        if isinstance(val, String):
            return IterableContains(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def walk(self, fn):
        fn(self)
        fn(self.vals)

    def __str__(self):
        return "[{}]".format(",".join(["`{}`".format(v) for v in self.vals]))


class Not(LogicMixin):
    def __init__(self, v):
        self.V = v

    def __str__(self):
        return "^({})".format(self.V)

    def walk(self, fn):
        fn(self)
        self.V.walk(fn)

    def traverse(self):
        return z3.Not(self.V.traverse())


class Eq(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return """({} == {})""".format(self.L, self.R)

    def traverse(self):
        # some object's compare is not trivial,
        # they might define their own compare
        compare = getattr(self.L, "compare", None)
        if compare:
            return compare(operator.eq, self.R.traverse())
        else:
            return self.L.traverse() == self.R.traverse()


class Or(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return """({} | {})""".format(self.L, self.R)

    def traverse(self):
        return z3.Or(self.L.traverse(), self.R.traverse())


class And(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def __str__(self):
        return """({} & {})""".format(self.L, self.R)

    def traverse(self):
        return z3.And(self.L.traverse(), self.R.traverse())

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)


class Xor(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return """({} ^ {})""".format(self.L, self.R)

    def traverse(self):
        return z3.Xor(self.L.traverse(), self.R.traverse())


class Concat(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return """({} + {})""".format(self.L, self.R)

    def traverse(self):
        return z3.Concat(self.L.traverse(), self.R.traverse())

    def __add__(self, val):
        if isinstance(val, str):
            return Concat(self, StringLiteral(val))
        if isinstance(val, String):
            return Concat(self, val)
        if isinstance(val, Concat):
            return Concat(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __radd__(self, val):
        if isinstance(val, str):
            return Concat(StringLiteral(val), self)
        if isinstance(val, String):
            return Concat(val, self)
        if isinstance(val, Concat):
            return Concat(val, self)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))


class Split(LogicMixin):
    def __init__(self, val, sep, before: bool):
        self.val = val
        self.sep = sep
        self.before = before

    def walk(self, fn):
        fn(self)
        self.val.walk(fn)
        self.sep.walk(fn)

    def __str__(self):
        return """({}.split({})""".format(self.val, self.sep)

    def traverse(self):
        v = self.val.traverse()
        index_end = z3.IndexOf(v, self.sep.traverse())
        if self.before:
            return z3.SubString(v, z3.IntVal(0), index_end)
        else:
            return z3.If(
                index_end > 0,
                z3.SubString(v, index_end + 1, z3.Length(self.val.traverse())),
                z3.StringVal(""),
            )


class Upper:
    def __init__(self, val):
        self.val = val

    def walk(self, fn):
        fn(self)
        self.val.walk(fn)

    def __str__(self):
        return """({}.upper()""".format(self.val)

    def traverse(self):
        return fn_string_upper(self.val.traverse())


class Lower:
    def __init__(self, val):
        self.val = val

    def walk(self, fn):
        fn(self)
        self.val.walk(fn)

    def __str__(self):
        return """({}.lower()""".format(self.val)

    def traverse(self):
        return fn_string_lower(self.val.traverse())


class Replace(LogicMixin):
    def __init__(self, val, src, dst):
        self.val = val
        self.src = src
        self.dst = dst

    def walk(self, fn):
        fn(self)
        self.val.walk(fn)
        self.src.walk(fn)
        self.dst.walk(fn)

    def __str__(self):
        return """({}.replace({}, {})""".format(self.val, self.src, self.dst)

    def traverse(self):
        return z3.Replace(self.val.traverse(), self.src.traverse(), self.dst.traverse())


class Lt(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return """({} < {})""".format(self.L, self.R)

    def traverse(self):
        # some object's compare is not trivial,
        # they might define their own compare
        compare = getattr(self.L, "compare", None)
        if compare:
            return compare(operator.lt, self.R.traverse())
        else:
            return self.L.traverse() < self.R.traverse()


class Gt(LogicMixin):
    def __init__(self, left, right):
        self.L = left
        self.R = right

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return """({} > {})""".format(self.L, self.R)

    def traverse(self):
        # some object's compare is not trivial,
        # they might define their own compare
        compare = getattr(self.L, "compare", None)
        if compare:
            return compare(operator.gt, self.R.traverse())
        else:
            return self.L.traverse() > self.R.traverse()


class StringMap:
    def __init__(self, name):
        self.name = name
        self.fn_map = z3.Function(self.name, z3.StringSort(), z3.StringSort())

    def __getitem__(self, key: String):
        """
        getitem used to build an expression, for example m[key] == "val"
        """
        # Map Index should impact function definition, aggregate it
        return MapIndex(self, key)

    def __str__(self):
        return """({} ^ {})""".format(self.L, self.R)

    def walk(self, fn):
        fn(self)


class MapIndex(LogicMixin):
    def __init__(self, m: StringMap, key: String):
        self.m = m
        self.key = key

    def __eq__(self, val):
        if isinstance(val, str):
            return Eq(self, StringLiteral(val))
        if isinstance(val, (String, Concat, Split, Replace)):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, str):
            return Not(Eq(self, StringLiteral(val)))
        if isinstance(val, (String, Concat, Split, Replace)):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __str__(self):
        return "{}[{}]".format(self.m.name, self.key)

    def traverse(self):
        return self.m.fn_map(z3.StringVal(self.key))

    def walk(self, fn):
        fn(self)


#
# See https://ericpony.github.io/z3py-tutorial/advanced-examples.htm
# for details on the advanced data types
#
StringList = z3.Datatype("List")
StringList.declare("cons", ("car", z3.StringSort()), ("cdr", StringList))
# nil list
StringList.declare("nil")
# Create the datatype
StringList = StringList.create()

fn_string_list_contains = z3.RecFunction(
    "string_list_contains", StringList, z3.StringSort(), z3.BoolSort()
)
fn_string_list_first = z3.RecFunction("string_list_first", StringList, z3.StringSort())
fn_string_list_contains_regex = z3.RecFunction(
    "string_list_contains_regex",
    StringList,
    z3.ReSort(z3.StringSort()),
    z3.BoolSort(),
)
fn_string_list_replace = z3.RecFunction(
    "string_list_replace", StringList, z3.StringSort(), z3.StringSort(), StringList
)
fn_string_list_add_if_not_exists = z3.RecFunction(
    "string_list_add_if_not_exists", StringList, z3.StringSort(), StringList
)

fn_string_upper = z3.RecFunction("string_upper", z3.StringSort(), z3.StringSort())

fn_string_lower = z3.RecFunction("string_lower", z3.StringSort(), z3.StringSort())


def string_list(vals: Iterable[String]):
    def iff(iterator):
        try:
            val = next(iterator)
        except StopIteration:
            return StringList.nil
        else:
            return StringList.cons(z3.StringVal(val), iff(iterator))

    return iff(iter(vals))


def define_string_list_contains():
    vals = z3.Const("string_list_contains_vals", StringList)
    element = z3.StringVal("string_list_contains_search")
    z3.RecAddDefinition(
        fn_string_list_contains,
        [vals, element],
        z3.If(
            StringList.nil == vals,
            z3.BoolVal(False),
            z3.If(
                StringList.car(vals) == element,
                z3.BoolVal(True),
                fn_string_list_contains(StringList.cdr(vals), element),
            ),
        ),
    )


def define_string_upper():
    element = z3.StringVal("string_upper_input")
    z3.RecAddDefinition(
        fn_string_upper,
        [element],
        z3.If(
            z3.Length(element) == 0,
            element,
            z3.Concat(
                z3.If(
                    z3.And(
                        z3.StrToCode(z3.SubString(element, 0, 1)) <= z3.StrToCode("z"),
                        z3.StrToCode(z3.SubString(element, 0, 1)) >= z3.StrToCode("a"),
                    ),
                    z3.StrFromCode(
                        z3.StrToCode(z3.SubString(element, 0, 1))
                        - (ord("a") - ord("A"))
                    ),
                    z3.SubString(element, 0, 1),
                ),
                fn_string_upper(z3.SubString(element, 1, z3.Length(element) - 1)),
            ),
        ),
    )


def define_string_lower():
    element = z3.StringVal("string_lower_input")
    z3.RecAddDefinition(
        fn_string_lower,
        [element],
        z3.If(
            z3.Length(element) == 0,
            element,
            z3.Concat(
                z3.If(
                    z3.And(
                        z3.StrToCode(z3.SubString(element, 0, 1)) <= z3.StrToCode("Z"),
                        z3.StrToCode(z3.SubString(element, 0, 1)) >= z3.StrToCode("A"),
                    ),
                    z3.StrFromCode(
                        z3.StrToCode(z3.SubString(element, 0, 1))
                        + (ord("a") - ord("A"))
                    ),
                    z3.SubString(element, 0, 1),
                ),
                fn_string_lower(z3.SubString(element, 1, z3.Length(element) - 1)),
            ),
        ),
    )


def define_string_list_first():
    vals = z3.Const("string_list_first_vals", StringList)
    z3.RecAddDefinition(
        fn_string_list_first,
        [vals],
        z3.If(
            StringList.nil == vals,
            z3.StringVal(""),
            z3.If(
                StringList.car(vals) != z3.StringVal(""),
                StringList.car(vals),
                fn_string_list_first(StringList.cdr(vals)),
            ),
        ),
    )


def define_string_list_contains_regex():
    vals = z3.Const("string_list_contains_regex_vals", StringList)
    expression = z3.Const(
        "string_list_contains_regex_expression", z3.ReSort(z3.StringSort())
    )
    z3.RecAddDefinition(
        fn_string_list_contains_regex,
        [vals, expression],
        z3.If(
            StringList.nil == vals,
            z3.BoolVal(False),
            z3.If(
                z3.InRe(StringList.car(vals), expression),
                z3.BoolVal(True),
                fn_string_list_contains_regex(StringList.cdr(vals), expression),
            ),
        ),
    )


def define_string_list_replace():
    vals = z3.Const("string_list_replace_vals", StringList)
    src = z3.StringVal("string_list_replace_src")
    dst = z3.StringVal("string_list_replace_dst")
    z3.RecAddDefinition(
        fn_string_list_replace,
        [vals, src, dst],
        z3.If(
            StringList.nil == vals,
            StringList.nil,
            StringList.cons(
                z3.Replace(StringList.car(vals), src, dst),
                fn_string_list_replace(StringList.cdr(vals), src, dst),
            ),
        ),
    )


def define_string_list_add_if_not_exists():
    vals = z3.Const("string_list_add_ifne_vals", StringList)
    element = z3.StringVal("string_add_ifne_contains_search")
    z3.RecAddDefinition(
        fn_string_list_add_if_not_exists,
        [vals, element],
        z3.If(
            fn_string_list_contains(vals, element) == z3.BoolVal(True),
            vals,
            StringList.cons(element, vals),
        ),
    )


define_string_list_contains()
define_string_list_contains_regex()
define_string_list_replace()
define_string_list_add_if_not_exists()
define_string_list_first()
define_string_upper()
define_string_lower()


class StringListWrapper:
    def __init__(self, vals: Iterable[String]):
        self.vals = vals

    def traverse(self):
        return string_list(self.vals)

    def walk(self, fn):
        fn(self)


class If:
    """
    If works like a functional style if:
       if(cond, eval_expression_on_true, eval_expression_on_false)
    """

    def __init__(self, cond, on_true, on_false):
        self.cond = cond
        self.on_true = on_true
        self.on_false = on_false

    def traverse(self):
        return z3.If(
            self.cond.traverse(), self.on_true.traverse(), self.on_false.traverse()
        )


class Case:
    def __init__(self, when, then):
        self.when = when
        self.then = convert_literal(then)

    def walk(self, fn):
        fn(self)
        fn(self.when)
        fn(self.then)


class Default:
    def __init__(self, expr):
        self.expr = convert_literal(expr)

    def walk(self, fn):
        fn(self)
        fn(self.expr)


def convert_literal(expr):
    if isinstance(expr, tuple):
        return StringListWrapper(expr)
    if isinstance(expr, str):
        return StringLiteral(expr)
    if isinstance(expr, int):
        return IntLiteral(expr)
    if isinstance(expr, bool):
        return BoolLiteral(expr)
    return expr


class Select:
    """
    Match works like a functional style select statement
       select(
           (case_1, eval_1),
           (case_2, eval_2),
           default
          )
    """

    def __init__(self, *expr):
        if len(expr) == 0:
            raise ParameterError("supply at least one case or default")
        default = 0
        for e in expr:
            if isinstance(e, Default):
                default += 1
            elif isinstance(e, Case):
                pass
            else:
                raise ParameterError("expected Default or Case, got {}", type(e))
        if default != 1:
            raise ParameterError("default statement is required at the end")
        # make sure it's the last
        if not isinstance(expr[len(expr) - 1], Default):
            raise ParameterError("supply at least one case or default")
        self.cases = expr[:-1]
        self.default = expr[-1]

    def __eq__(self, val):
        return Eq(self, convert_literal(val))

    def __ne__(self, val):
        return Not(Eq(self, convert_literal(val)))

    def walk(self, fn):
        fn(self)
        for e in self.cases:
            e.walk(fn)
        self.default.walk(fn)

    def traverse(self):
        def iterate(i):
            try:
                case = next(i)
            except StopIteration:
                return self.default.expr.traverse()
            else:
                return z3.If(
                    case.when.traverse(),
                    case.then.traverse(),
                    iterate(i),
                )

        return iterate(iter(self.cases))


class StringSetMap:
    """
    Map of string sets:

    'key': set("a", "b", "c")
    """

    def __init__(self, name: str, values: typing.Dict = None):
        self.name = name

        if values is None:
            self.fn_map = z3.Function(self.name, z3.StringSort(), StringList)
        else:
            # if string set map is defined, instead of unbound function as above,
            # define the map as a recursive function
            def iff(fn_key, iterator):
                try:
                    key, val = next(iterator)
                    if isinstance(val, tuple):
                        val = StringListWrapper(val)
                except StopIteration:
                    return StringList.nil
                else:
                    return z3.If(
                        fn_key == z3.StringVal(key),
                        val.traverse(),
                        iff(fn_key, iterator),
                    )
                    return StringList.cons(z3.StringVal(val), iff(iterator))

            # wrap the original map function to always add a key if it exists
            arg_key = z3.StringVal(self.name + "string_set_map_add_key")
            self.fn_map = z3.RecFunction(self.name, z3.StringSort(), StringList)
            z3.RecAddDefinition(
                self.fn_map, [arg_key], iff(arg_key, iter(values.items()))
            )

    def __getitem__(self, key: String):
        """
        getitem used to build an expression, for example m[key].contains("val")
        """
        # Map Index should impact function definition, aggregate it
        return StringSetMapIndex(self, key)

    def add_value(self, key: String, val: String):
        return StringSetMapAddValue(self, key, val)

    def remove_keys(self, *keys: String):
        return StringSetMapRemoveKeys(self, keys)

    def overwrite(self, values: typing.Dict):
        return StringSetMapOverwrite(self, values)

    def __str__(self):
        return """({} ^ {})""".format(self.L, self.R)

    def walk(self, fn):
        fn(self)

    def traverse(self):
        return self.fn_map


class StringSetMapOverwrite(StringSetMap):
    def __init__(self, m: StringSetMap, values: typing.Dict):
        self.m = m
        self.name = m.name + "_overwrite"
        self.V = values

        # wrap the original map function to always add a key if it exists
        arg_key = z3.StringVal(self.name + "_string_set_map_overwrite")
        self.fn_map = z3.RecFunction(self.name, z3.StringSort(), StringList)

        # define the map as a recursive function
        def iff(fn_key, iterator, wrapped_map_fn):
            try:
                key, val = next(iterator)
                if isinstance(val, tuple):
                    val = StringListWrapper(val)
            except StopIteration:
                return wrapped_map_fn(fn_key)
            else:
                return z3.If(
                    fn_key == z3.StringVal(key),
                    val.traverse(),
                    iff(fn_key, iterator, wrapped_map_fn),
                )

        # wrap the original map function to always add a key if it exists
        arg_key = z3.StringVal(self.name + "_string_set_map_extend_arg")
        self.fn_map = z3.RecFunction(self.name, z3.StringSort(), StringList)
        z3.RecAddDefinition(
            self.fn_map, [arg_key], iff(arg_key, iter(values.items()), self.m.fn_map)
        )

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.overwrite({}))""".format(self.name, self.V)

    def traverse(self):
        return self.fn_map

    def __getitem__(self, key: String):
        """
        getitem used to build an expression, for example m[key].contains("val")
        """
        # Map Index should impact function definition, aggregate it
        return StringSetMapIndex(self, key)

    def add_value(self, key: String, val: String):
        return StringSetMapAddValue(self, key, val)


class StringSetMapAddValue(StringSetMap):
    def __init__(self, m: StringSetMap, key, val):
        self.m = m
        self.name = m.name + "_add_value"
        self.K = key
        self.V = val

        # wrap the original map function to always add a key if it exists
        arg_key = z3.StringVal(self.name + "string_set_map_add_key")
        self.fn_map = z3.RecFunction(self.name, z3.StringSort(), StringList)
        z3.RecAddDefinition(
            self.fn_map,
            [arg_key],
            z3.If(
                arg_key == z3.StringVal(key),
                z3.If(
                    fn_string_list_contains(self.m.fn_map(arg_key), z3.StringVal(val)),
                    self.m.fn_map(arg_key),
                    StringList.cons(z3.StringVal(val), self.m.fn_map(arg_key)),
                ),
                self.m.fn_map(arg_key),
            ),
        )

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.K.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.add({}, {}))""".format(self.m.name, self.K, self.V)

    def traverse(self):
        return self.fn_map

    def __getitem__(self, key: String):
        """
        getitem used to build an expression, for example m[key].contains("val")
        """
        # Map Index should impact function definition, aggregate it
        return StringSetMapIndex(self, key)

    def add_value(self, key: String, val: String):
        return StringSetMapAddValue(self, key, val)


class StringSetMapRemoveKeys(StringSetMap):
    def __init__(self, m: StringSetMap, keys):
        self.m = m
        self.name = m.name + "_remove_keys"
        self.K = keys

        arg_key = z3.StringVal(self.name + "string_set_map_remove_key")
        self.fn_map = z3.RecFunction(self.name, z3.StringSort(), StringList)
        # wrap the original map function to always return a nil list if key matches,
        # return original function otherwise
        z3.RecAddDefinition(
            self.fn_map,
            [arg_key],
            z3.If(
                z3.Or([arg_key == z3.StringVal(key) for key in self.K]),
                StringList.nil,
                self.m.fn_map(arg_key),
            ),
        )

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.K.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.remove_keys({}))""".format(self.m.name, self.K)

    def traverse(self):
        return self.fn_map

    def __getitem__(self, key: String):
        """
        getitem used to build an expression, for example m[key].contains("val")
        """
        # Map Index should impact function definition, aggregate it
        return StringSetMapIndex(self, key)

    def add_value(self, key: String, val: String):
        return StringSetMapAddValue(self, key, val)


class StringSetMapIndex:
    def __init__(self, m: StringSetMap, key: String):
        self.m = m
        self.key = key

    def first(self):
        """
        First returns first non-empty value
        """
        return StringSetMapIndexFirst(self)

    def contains(self, val):
        if isinstance(val, str):
            return StringSetMapIndexContains(self, StringLiteral(val))
        if isinstance(val, (String, MapIndex)):
            return StringSetMapIndexContains(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def contains_regex(self, val):
        if isinstance(val, str):
            return StringSetMapIndexContainsRegex(self, parse_regex(val))
        raise TypeError(
            "unsupported type {}, supported strings with regexp only".format(type(val))
        )

    def replace(self, src, dst):
        if isinstance(src, str):
            return StringSetMapIndexReplace(
                self, StringLiteral(src), StringLiteral(dst)
            )
        if isinstance(dst, String):
            return StringSetMapIndexReplace(self, src, dst)
        raise TypeError("unsupported type {}, supported strings only".format(type(src)))

    def add(self, val):
        if isinstance(val, str):
            return StringSetMapIndexAdd(self, StringLiteral(val))
        if isinstance(val, String):
            return StringSetMapIndexAdd(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def walk(self, fn):
        fn(self)

    def __eq__(self, val):
        if isinstance(val, tuple):
            return StringSetMapIndexEquals(self, StringTuple(val))
        raise TypeError(
            "unsupported type {}, supported string tuples only".format(type(val))
        )

    def traverse(self):
        return self.m.fn_map(z3.StringVal(self.key))


class StringSetMapIndexContains(LogicMixin):
    def __init__(self, expr: StringSetMapIndex, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.contains({}))""".format(self.E, self.V)

    def traverse(self):
        return fn_string_list_contains(
            self.E.m.fn_map(z3.StringVal(self.E.key)), self.V.traverse()
        ) == z3.BoolVal(True)


class StringSetMapIndexFirst:
    def __init__(self, expr: StringSetMapIndex):
        self.E = expr

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)

    def __str__(self):
        return """({}.first())""".format(self.E)

    def traverse(self):
        return fn_string_list_first(self.E.m.fn_map(z3.StringVal(self.E.key)))

    def __eq__(self, val):
        if isinstance(val, str):
            return Eq(self, StringLiteral(val))
        if isinstance(val, (String, Concat, Split, Replace, StringSetMapIndexFirst)):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, str):
            return Not(Eq(self, StringLiteral(val)))
        if isinstance(val, (String, Concat, Split, Replace, StringSetMapIndexFirst)):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))


class StringSetMapIndexContainsRegex(LogicMixin):
    def __init__(self, expr: StringSetMapIndex, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.contains_regex({}))""".format(self.E, self.V)

    def traverse(self):
        return fn_string_list_contains_regex(
            self.E.m.fn_map(z3.StringVal(self.E.key)), self.V.traverse()
        ) == z3.BoolVal(True)


class StringSetMapIndexReplace:
    def __init__(self, expr: StringSetMapIndex, src, dst):
        self.E = expr
        self.S = src
        self.D = dst

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.S.walk(fn)
        self.D.walk(fn)

    def __str__(self):
        return """({}.replace({}, {}))""".format(self.E, self.S, self.D)

    def traverse(self):
        return fn_string_list_replace(
            self.E.m.fn_map(z3.StringVal(self.E.key)),
            self.S.traverse(),
            self.D.traverse(),
        )


class StringSetMapIndexAdd:
    def __init__(self, expr: StringSetMapIndex, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}.add({}))""".format(self.E, self.V)

    def traverse(self):
        return fn_string_list_add_if_not_exists(
            self.E.m.fn_map(z3.StringVal(self.E.key)), self.V.traverse()
        )


class StringSetMapIndexEquals(LogicMixin):
    def __init__(self, expr: StringSetMapIndex, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return """({}[{}] == {})""".format(self.E.m.name, self.E.key, self.V.vals)

    def traverse(self):
        return self.E.m.fn_map(z3.StringVal(self.E.key)) == string_list(self.V.vals)


def collect_symbols(s, expr):
    if isinstance(expr, (String, Int, Duration, Bool, StringEnum)):
        s.add(expr.name)
    if isinstance(expr, MapIndex):
        s.add(expr.m.name + "." + expr.key)


def collect_names(s, expr):
    if isinstance(expr, (String, Int, Duration, Bool, StringEnum)):
        s.add(expr.name)
    if isinstance(expr, MapIndex):
        s.add(expr.m.name)


class Predicate:
    def __init__(self, expr, loud=True):
        self.symbols = set()
        self.expr = expr
        self.expr.walk(functools.partial(collect_symbols, self.symbols))
        self.loud = loud

    def __str__(self):
        return self.expr.__str__()

    def traverse(self):
        return self.expr.traverse()

    def walk(self, fn):
        self.expr.walk(fn)

    def verify(self):
        solver = z3.Solver()
        solver.add(self.expr.traverse())
        if solver.check() == z3.unsat:
            raise ParameterError("our own predicate is unsolvable")

    def check(self, other):
        """
        check checks the predicate against conditions specified in
        another predicate. Both predicates should define
        """
        # sanity check - to check two predicates, they should
        # define the same sets of symbols
        if not self.symbols.issubset(other.symbols):
            diff = self.symbols.difference(other.symbols)
            raise ParameterError(
                """check can not resolve ambiguity, predicates use different symbols %s and %s, diff: %s,
                add missing symbols in the predicate checked against to proceed with check"""
                % (self.symbols, other.symbols, diff)
            )

        return self.solves_with(other)

    def query(self, other):
        """
        Query can only succeed if symbols in the query are a strict subset
        of all symbols used in the predicate being queried
        Query behaves like SQL, e.g. select * from users where name like 'a%';
        """
        if not other.symbols.issubset(self.symbols):
            diff = self.symbols.difference(other.symbols)
            return (
                False,
                """check can not resolve ambiguity, query uses symbols %s that are not present in predicate %s, diff: %s,
                query must be a subset of symbols of the predicate"""
                % (self.symbols, other.symbols, diff),
            )
        return self.solves_with(other)

    def solve(self):
        """
        Solve solves predicate against itself
        """
        solver = z3.Solver()
        e = self.expr.traverse()
        if self.loud:
            print("OUR EXPR: {}".format(e))
        solver.add(self.expr.traverse())

        if solver.check() == z3.unsat:
            raise ParameterError("our own predicate is unsolvable")
        return (True, solver.model())

    def solves_with(self, other):
        """
        solves_with returns true if the predicate can be true with another
        predicate being true at the same time.
        """
        solver = z3.Solver()
        e = self.expr.traverse()
        if self.loud:
            print("OUR EXPR: {}".format(e))
        solver.add(self.expr.traverse())

        if solver.check() == z3.unsat:
            raise ParameterError("our own predicate is unsolvable")
        o = other.expr.traverse()
        if self.loud:
            print("THEIR EXPR: {}".format(o))
        solver.add(other.expr.traverse())

        # TODO do a second pass to build a key checking function
        # for both predicates!
        self.expr.walk(functools.partial(collect_symbols, self.symbols))

        if solver.check() == z3.unsat:
            return (False, "predicate is unsolvable against %s" % (other.expr,))
        return (True, solver.model())

    def equivalent(self, other):
        solver = z3.Solver()
        solver.add(z3.Distinct(self.expr.traverse(), other.expr.traverse()))
        result = solver.check()
        if z3.unsat == result:
            return (True, "Predicates are equivalent")
        elif z3.sat == result:
            return (
                False,
                f"Predicates are not equivalent; counterexample: {solver.model()}",
            )
        else:
            return (False, str(result))

    def simplify(self):
        """
        Simplify is just an example. It splits expression into subexpressoins.
        If an expression renders equivalent results with left or right tree branch of or, and
        then it removes the redundant one.
        """

        def split(vals, expr):
            if type(expr) == And or type(expr) == Or:
                vals.append(expr.L)
                vals.append(expr.R)

        expr = self.expr
        while True:
            v = []
            expr.walk(functools.partial(split, v))
            if len(v) == 0:
                return Predicate(expr)
            left, right = Predicate(v[0]), Predicate(v[1])
            equiv, _ = left.equivalent(right)
            if equiv:
                expr = left
            else:
                return Predicate(expr)
