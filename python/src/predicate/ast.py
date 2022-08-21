import z3
import operator
import typing
import re

from functools import partial
from collections.abc import Iterable
from dataclasses import dataclass

from .errors import ParameterError

# reference
# https://z3prover.github.io/api/html/namespacez3py.html
class StringLiteral:
    def __init__(self, val:str):
        self.V = val

    def traverse(self):
        return z3.StringVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return '`{}`'.format(self.V)

    
class IntLiteral:
    def __init__(self, val: int):
        self.V = val

    def traverse(self):
        return z3.IntVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return '`{}`'.format(self.V)

NANOSECOND = 1
MICROSECOND = 1000 * NANOSECOND
MILLISECOND = 1000 * MICROSECOND
SECOND = 1000 * MILLISECOND
MINUTE = 60 * SECOND
HOUR= 60 * MINUTE


class DurationLiteral:
    '''
    Duration literal measures time in nanoseconds
    '''
    def __init__(self, val: int):
        self.V = val


    def traverse(self):
        return z3.IntVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return '`{}`'.format(self.V)


class BoolLiteral:
    '''
    Boolean literal is true or false
    '''
    def __init__(self, val: bool):
        self.V = val

    def traverse(self):
        return z3.BoolVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return '`{}`'.format(self.V)


class Int:
    def __init__(self, name):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.IntSort())

    def __eq__(self, val):
        if isinstance(val, int):
            return Eq(self, IntLiteral(val))
        if isinstance(val, (Int,)):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, int):
            return Not(Eq(self, IntLiteral(val)))
        if isinstance(val, (Int,)):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __lt__(self, val):
        if isinstance(val, int):
            return Lt(self, IntLiteral(val))
        if isinstance(val, (Int,)):
            return Lt(self, val)
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __gt__(self, val):
        if isinstance(val, int):
            return Gt(self, IntLiteral(val))
        if isinstance(val, (Int,)):
            return Gt(self, val)
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)

    def __str__(self):
        return 'int({})'.format(self.name)

class Duration:
    def __init__(self, name):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.IntSort())

    def traverse(self):
        return self.fn(z3.StringVal(self.name))
        
    def walk(self, fn):
        fn(self)

    def __str__(self):
        return 'duration({})'.format(self.name)

    @staticmethod
    def new(hours=0, minutes=0, seconds=0, milliseconds=0, microseconds=0, nanoseconds=0):
        return DurationLiteral(hours * HOUR +
                               minutes * MINUTE +
                               seconds * SECOND +
                               milliseconds * MILLISECOND +
                               microseconds * MICROSECOND +
                               nanoseconds * NANOSECOND)

    def __eq__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __lt__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Lt(self, val)
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __gt__(self, val):
        if isinstance(val, (Duration, DurationLiteral)):
            return Gt(self, val)
        raise TypeError("unsupported type {}, supported duration and duration literals only".format(type(val)))        

class Bool:
    def __init__(self, name):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.BoolSort())

    def __eq__(self, val):
        if isinstance(val, bool):
            return Eq(self, BoolLiteral(val))
        if isinstance(val, (Bool,)):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, bool):
            return Not(Eq(self, BoolLiteral(val)))
        if isinstance(val, (Bool,)):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported integers only".format(type(val)))

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)

    def __str__(self):
        return 'bool({})'.format(self.name)

class String:
        
    def __init__(self, name):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.StringSort())

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

    def __add__(self, val):
        if isinstance(val, str):
            return Concat(self, StringLiteral(val))
        if isinstance(val, (String, Concat, Split, Replace)):
            return Concat(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __radd__(self, val):
        if isinstance(val, str):
            return Concat(StringLiteral(val), self)
        if isinstance(val, (String, Concat, Split, Replace)):
            return Concat(val, self)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def before_delimiter(self, sep:str):
        '''
        '''
        return Split(self, StringLiteral(sep), before=True)

    def after_delimiter(self, sep:str):
        '''
        '''
        return Split(self, StringLiteral(sep), before=False)

    def replace(self, src: str, dst:str):
        '''
        '''
        return Replace(self, StringLiteral(src), StringLiteral(dst))

    def __str__(self):
        return 'string({})'.format(self.name)

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)


class IterableContains:
    def __init__(self, expr: Iterable, val):
        self.E = expr
        self.V = val

    def walk(self, fn):
        fn(self)
        self.E.walk(fn)
        self.V.walk(fn)

    def __str__(self):
        return '''({}.contains({}))'''.format(self.E, self.V)

    def traverse(self):
        return z3.Or(*[
            StringLiteral(v).traverse() == self.V.traverse()
            for v in self.E.vals
        ])

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)    

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

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
        return '[{}]'.format(",".join(['`{}`'.format(v) for v in self.vals]))

class Not:
    def __init__(self, v):
        self.V = v

    def __str__(self):
        return '^({})'.format(self.V)

    def walk(self, fn):
        fn(self)
        self.V.walk(fn)
    
    def traverse(self):
        return z3.Not(self.V.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

class Eq:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return '''({} == {})'''.format(self.L, self.R)

    def traverse(self):
        # some object's compare is not trivial,
        # they might define their own compare
        compare = getattr(self.L, "compare", None)
        if compare:
            return compare(operator.eq, self.R.traverse())
        else:
            return self.L.traverse() == self.R.traverse()

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)    

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

class Or:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return '''({} | {})'''.format(self.L, self.R)

    def traverse(self):
        return z3.Or(self.L.traverse(), self.R.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __Xor__(self, other):
        return Xor(self, other)    

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

class And:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def __str__(self):
        return '''({} & {})'''.format(self.L, self.R)

    def traverse(self):
        return z3.And(self.L.traverse(), self.R.traverse())

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)    

    def __and__(self, other):
        return And(self, other)    

    def __invert__(self):
        return Not(self)

class Xor:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return '''({} ^ {})'''.format(self.L, self.R)

    def traverse(self):
        return z3.Xor(self.L.traverse(), self.R.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)    

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

class Concat:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return '''({} + {})'''.format(self.L, self.R)

    def traverse(self):
        return z3.Concat(self.L.traverse(), self.R.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

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

class Split:
    def __init__(self, val, sep, before: bool):
        self.val = val
        self.sep = sep
        self.before = before

    def walk(self, fn):
        fn(self)
        self.val.walk(fn)
        self.sep.walk(fn)

    def __str__(self):
        return '''({}.split({})'''.format(self.val, self.sep)

    def traverse(self):
        v = self.val.traverse()
        index_end = z3.IndexOf(v, self.sep.traverse())
        if self.before:
            return z3.SubString(
                v, z3.IntVal(0), index_end
            )
        else:
            return z3.If(index_end > 0,
                  z3.SubString(
                      v, index_end + 1, z3.Length(self.val.traverse())
                  ),
                  z3.StringVal(""))

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

class Replace:
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
        return '''({}.replace({}, {})'''.format(self.val, self.src, self.dst)

    def traverse(self):
        return z3.Replace(
            self.val.traverse(),
            self.src.traverse(),
            self.dst.traverse()
        )

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)


class Lt:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return '''({} < {})'''.format(self.L, self.R)

    def traverse(self):
        return self.L.traverse() < self.R.traverse()

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

class Gt:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def walk(self, fn):
        fn(self)
        self.L.walk(fn)
        self.R.walk(fn)

    def __str__(self):
        return '''({} < {})'''.format(self.L, self.R)

    def traverse(self):
        return self.L.traverse() > self.R.traverse()

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)


class StringMap:
    def __init__(self, name):
        self.name = name
        self.fn_map = z3.Function(self.name, z3.StringSort(), z3.StringSort())

    def __getitem__(self, key: String):
        '''
        getitem used to build an expression, for example m[key] == "val"
        '''
        # Map Index should impact function definition, aggregate it
        return MapIndex(self, key)

    def __str__(self):
        return '''({} ^ {})'''.format(self.L, self.R)

    def walk(self, fn):
        fn(self)    


class MapIndex:
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

    def __or__(self, other):
        return Or(self, other)

    def __xor__(self, other):
        return Xor(self, other)    

    def __and__(self, other):
        return And(self, other)

    def __invert__(self):
        return Not(self)

    def __str__(self):
        return '{}[{}]'.format(self.m.name, self.key)

    def traverse(self):
        return self.m.fn_map(z3.StringVal(self.key))

    def walk(self, fn):
        fn(self)




def collect_symbols(s, expr):
    if isinstance(expr, (String, Int, Duration, Bool)):
        s.add(expr.name)
    if isinstance(expr, MapIndex):
        s.add(expr.m.name + "." + expr.key)

def collect_names(s, expr):
    if isinstance(expr, (String, Int, Duration, Bool)):
        s.add(expr.name)
    if isinstance(expr, MapIndex):
        s.add(expr.m.name)

class Predicate:
    def __init__(self, expr):
        self.symbols = set()
        self.expr = expr
        self.expr.walk(partial(collect_symbols, self.symbols))

    def __str__(self):
        return self.expr.__str__()

    def walk(self, fn):
        self.expr.walk(fn)

    def verify(self):
        solver = z3.Solver()
        solver.add(self.expr.traverse())
        if solver.check() == z3.unsat:
            raise ParameterError('our own predicate is unsolvable')

    def check(self, other):
        '''
        check checks the predicate against conditions specified in
        another predicate. Both predicates should define 
        '''
        # sanity check - to check two predicates, they should
        # define the same sets of symbols
        if not self.symbols.issubset(other.symbols):
            diff = self.symbols.difference(other.symbols)            
            raise ParameterError(
                '''check can not resolve ambiguity, predicates use different symbols %s and %s, diff: %s,
                add missing symbols in the predicate checked against to proceed with check''' % (self.symbols, other.symbols, diff))

        return self.solves_with(other)

    def query(self, other):
        '''
        Query can only succeed if symbols in the query are a strict subset
        of all symbols used in the predicate being queried
        Query behaves like SQL, e.g. select * from users where name like 'a%';
        '''
        if not other.symbols.issubset(self.symbols):
            diff = self.symbols.difference(other.symbols)
            return (False,
                '''check can not resolve ambiguity, query uses symbols %s that are not present in predicate %s, diff: %s,
                query must be a subset of symbols of the predicate''' % (self.symbols, other.symbols, diff))
        return self.solves_with(other)

    def solves_with(self, other):
        '''
        solves_with returns true if the predicate can be true with another
        predicate being true at the same time.
        '''
        solver = z3.Solver()
        solver.add(self.expr.traverse())
        
        if solver.check() == z3.unsat:
            raise ParameterError('our own predicate is unsolvable')
        solver.add(other.expr.traverse())

        # TODO do a second pass to build a key checking function
        # for both predicates!
        self.expr.walk(partial(collect_symbols, self.symbols))
                
        if solver.check() == z3.unsat:
            return (False, "predicate is unsolvable against %s" % (other.expr, ))
        return (True, solver.model())    

    def equivalent(self, other):
        solver = z3.Solver()
        solver.add(z3.Distinct(self.expr.traverse(), other.expr.traverse()))
        result = solver.check()
        if z3.unsat == result:
            return (True, "Predicates are equivalent")
        elif z3.sat == result:
            return (False, f"Predicates are not equivalent; counterexample: {solver.model()}")
        else:
            return (False, str(result))

    def simplify(self):
        '''
        Simplify is just an example. It splits expression into subexpressoins.
        If an expression renders equivalent results with left or right tree branch of or, and
        then it removes the redundant one.
        '''
        
        def split(vals, expr):
            if type(expr) == And or type(expr) == Or:
                vals.append(expr.L)
                vals.append(expr.R)

        expr = self.expr
        while True:
            v = []
            expr.walk(partial(split, v))
            if len(v) == 0:
                return Predicate(expr)
            left, right = Predicate(v[0]), Predicate(v[1])
            equiv, _ = left.equivalent(right)
            if equiv:
                expr = left
            else:
                return Predicate(expr)


