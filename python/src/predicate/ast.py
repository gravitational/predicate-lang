import z3
from functools import partial
import operator
from .errors import ParameterError
from collections.abc import Iterable
from dataclasses import dataclass

# reference
# https://z3prover.github.io/api/html/namespacez3py.html

class StringLiteral:
    def __init__(self, val):
        self.V = val

    def traverse(self):
        return z3.StringVal(self.V)

    def walk(self, fn):
        fn(self)
        fn(self.V)

    def __str__(self):
        return '`{}`'.format(self.V)

class String:
        
    def __init__(self, name):
        self.name = name
        self.fn = z3.Function(self.name, z3.StringSort(), z3.StringSort())

    def __eq__(self, val):
        if isinstance(val, str):
            return Eq(self, StringLiteral(val))
        if isinstance(val, String):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, str):
            return Not(Eq(self, StringLiteral(val)))
        if isinstance(val, String):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))    

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
        return '[{}]'.format(['`{}`'.format(v) for v in self.vals].join(", "))

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


def define_mapfn(fn_map, fn_key, kv: dict[String, String]):
    """
    Define mapfn defines a key value map using recursive Z3 function,
    essentially converting {'a': 'b'} into if x == 'a' then 'b' else ...
    """
    def iff(iterator):
        try:
            key, val = next(iterator)
        except StopIteration:
            return z3.StringVal("")
        else:
            return z3.If(
                fn_key == z3.StringVal(key),
                z3.StringVal(val),
                iff(iterator)
            )
    z3.RecAddDefinition(
        fn_map,
        fn_key,
        iff(iter(kv.items()))
       )

class Map:
    def __init__(self, name, kv: dict[String, String]):
        self.kv = kv
        self.name = name
        self.fn_map = z3.RecFunction(self.name, z3.StringSort(), z3.StringSort())
        self.fn_key = z3.String(self.name + "_key")
        define_mapfn(self.fn_map, self.fn_key, self.kv)

    def get(self, key: String):
        '''
        get works like a classic map.get or a function call:
        we have to build model by giving it a condition that works
        and then we can eval model with an argument
        '''
        s = z3.Solver()
        s.add(self.fn_map(self.fn_key) != z3.StringVal(""))
        if s.check() == z3.unsat:
            raise KeyError("map is empty")
        return s.model().eval(self.fn_map(z3.StringVal(key)))

    def __getitem__(self, key: String):
        '''
        getitem used to build an expression, for example m[key] == "val"
        '''
        return MapIndex(self, key)

class MapIndex:
    def __init__(self, m: Map, key: String):
        self.m = m
        self.key = key

    def __eq__(self, val):
        if isinstance(val, str):
            return Eq(self, StringLiteral(val))
        if isinstance(val, String):
            return Eq(self, val)
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))

    def __ne__(self, val):
        if isinstance(val, str):
            return Not(Eq(self, StringLiteral(val)))
        if isinstance(val, String):
            return Not(Eq(self, val))
        raise TypeError("unsupported type {}, supported strings only".format(type(val)))    

    def __str__(self):
        return '{}[{}]'.format(self.m.name, self.key)

    def compare(self, op, val):
        return z3.And(op(self.m.fn_key, self.key), self.m.fn_map(self.m.fn_key) == val)

    def traverse(self):
        return self.m.fn_map(self.m.fn_key) != z3.StringVal("")

    def walk(self, fn):
        fn(self)
        

def collect_symbols(s, expr):
    if type(expr) == String:
        s.add(expr.name)

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
        Check checks the predicate against another predicate
        '''
        # sanity check - to check two predicates, they should
        # define the same sets of symbols
        diff = self.symbols.difference(other.symbols)
        if len(diff) != 0:
            raise ParameterError(
                '''check can not resolve ambiguity, predicates use different symbols %s and %s, diff: %s,
                add missing symbols in both predicates to proceed with check''' % (self.symbols, other.symbols, diff))

        return self.query(other)

    def query(self, other):
        '''
        Query checks if the predicate could satisfy with the other predicate that holds true.
        '''
        solver = z3.Solver()
        solver.add(self.expr.traverse())
        if solver.check() == z3.unsat:
            raise ParameterError('our own predicate is unsolvable')

        solver.add(other.expr.traverse())
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


