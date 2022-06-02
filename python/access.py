import z3
from functools import partial
import operator

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
        return 'String({})'.format(self.name)

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

    def walk(self, fn):
        fn(self)


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


def define_mapfn(fn_map, fn_param, kv: dict[String, String]):
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
                fn_param == z3.StringVal(key),
                z3.StringVal(val),
                iff(iterator)
            )
    z3.RecAddDefinition(
        fn_map,
        fn_param,
        iff(iter(kv.items()))
       )

class Map:
    def __init__(self, name, kv: dict[String, String]):
        self.kv = kv
        self.name = name
        self.fn_map = z3.RecFunction(self.name, z3.StringSort(), z3.StringSort())
        self.fn_x = z3.String(self.name + "_x")
        define_mapfn(self.fn_map, self.fn_x, self.kv)

    def get(self, key: String):
        '''
        get works like a classic map.get or a function call:
        we have to build model by giving it a condition that works
        and then we can eval model with an argument
        '''
        s = z3.Solver()
        s.add(self.fn_map(self.fn_x) != z3.StringVal(""))
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
        return z3.And(op(self.m.fn_x, self.key), self.m.fn_map(self.m.fn_x) == val)

    def traverse(self):
        return self.m.fn_map(self.m.fn_x) != z3.StringVal("")

    def walk(self, fn):
        fn(self)
        

def collect_symbols(s, expr):
    if type(expr) == String:
        s.add(expr.name)

class ParameterError(Exception):
    pass

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


# User-defined models here
class Server:
    '''
    Server is a domain-specific model (e.g. Teleport server)
    '''
    env = String("server.env")
    # login is SSH server login
    login = String("server.login")

class User:
    '''
    User is a domain specific model (e.g. Teleport user)
    '''
    team = String("user.team")
    # name is username
    name = String("user.name")


p = Predicate(
    User.team == "stage"
)

ret = p.check(Predicate(User.team != "stage"))
print(ret)

# predicate is equivalent to itself
print(p.equivalent(p))

# predicate is equivalent to it's redundant version
print(p.equivalent(Predicate((User.team == "stage") | (User.team == "stage"))))

# this predicate uses two symbols
p = Predicate(Server.env == User.team)

# holds
ret = p.check(Predicate((Server.env == "prod") & (User.team == "prod")))
print(ret)

# user is not defined, in the other predicate the check should fail
try:
    p.check(Predicate(Server.env == "stage"))
except ParameterError:
    pass
else:
    assert "expected to fail"

## Try to simplify redundant obvious expression
p = Predicate(
    (User.team == "stage") | (User.team == "stage")
)
print(p.simplify())

## Simplify on non obvious expression is no-op
p = Predicate(
    (User.team == "stage") | (Server.env == "stage")
)
print(p.simplify())

## Let's build more complex expressions
## Any user can access servers marked with their team with their username

p = Predicate((Server.env == User.team) & (Server.login == User.name))

# Bob can access server with label prod with his name
ret, _ = p.check(
    Predicate((Server.env == "prod") & (User.team == "prod") & (User.name == "bob") & (Server.login == "bob"))
)
print(ret)

# Query helps to ask more broad questions, e.g. can bob access servers labeled as "prod"?
ret, _ = p.query(
    Predicate((Server.env == "prod") & (User.team == "prod") & (User.name == "bob")))
print("Can bob access servers labeled as prod?", ret)

# Can bob access servers labeled as stage?
ret, _ = p.query(
    Predicate((Server.env == "stage") & (User.team == "prod") & (User.name == "bob")))
print("Can bob access servers labeled as stage?", ret)

# Bob can't access server prod with someone else's name
ret, _ = p.check(
    Predicate((Server.env == "prod") & (User.team == "prod") & (User.name == "bob") & (Server.login == "jim"))
)
print(ret)

# Bob can't access server prod if Bob's team is not valid
ret, _ = p.check(
    Predicate((Server.env == "prod") & (User.team == "stage") & (User.name == "bob") & (Server.login == "bob"))
)
print(ret)

## No user except alice can get prod servers as root,
## For security invariant to hold, it has to be & with other rules
prod = (Server.env == "prod") & (Server.login == "root")
root = ((User.name == "alice") & prod)

# "Deny condition if x" <==> condition & ~x
general = ((User.team == Server.env) & (Server.login == User.name) & ~ prod)
p = Predicate(
    root | general
)

# Alice can access prod as root
ret, _ = p.check(
    Predicate((Server.env == "prod") & (User.name == "alice") & (Server.login == "root") & (User.team == "noop") )
)
print("Alice can access prod as root:", ret)

# Bob can access stage as his name
ret, _ = p.check(
    Predicate((Server.env == "stage") & (User.name == "bob") & (Server.login == "bob") & (User.team == "stage") )
)
print("Bob can access stage with his name:", ret)

# Bob can't access prod as root
ret, _ = p.check(
    Predicate((Server.env == "prod") & (User.name == "bob") & (Server.login == "root") & (User.team == "prod") )
)
print("Bob can access prod as root:", ret)

# Queries:

ret, _ = p.query(
    Predicate((Server.env == "prod") & (Server.login == "root")))
print("Is it possible to access prod as root?", ret)

# Is it possible for bob to access prod as root?
ret, _ = p.query(
    Predicate((Server.env == "prod") & (Server.login == "root") & (User.name == "bob")))
print("Can bob access prod as root?", ret)

# Is it possible for anyone who is not alice to access prod as root
# <- This could be a linter checker
ret, _ = p.query(
    Predicate((Server.env == "prod") & (Server.login == "root") & (User.name != "alice")))
print("Is it possible for anyone who is not alice to access prod as root?", ret)

# try the case that contradicts the predicate
violation = ((User.name == "jim") & (Server.env == "prod") & (Server.login == "root")  & ~prod)
p = Predicate(
    root | violation
)

# Jim can access prod as root
ret, _ = p.check(
    Predicate((Server.env == "prod") & (User.name == "jim") & (Server.login == "root") & (User.team == "noop") )
)
print("Jim can access prod as root:", ret)

# This is experiment with maps
m = Map('mymap', {'key': 'val'})
# maps can work like usual maps, with get working (but being slow)
print("mymap[key]==", m.get('key'))

# maps could be part of the predicate
p = Predicate(
    m["key"] == "val"
)
ret = p.query(Predicate(m["key"] == "val"))
print(ret)

#
# TODO: sets, regexps, arrays?
# TODO: map from one set to another set (regexps? functions?)
# TODO: Transpile to teleport roles, IWS IAM roles
# 
