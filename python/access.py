import z3

# reference
# https://z3prover.github.io/api/html/namespacez3py.html

class StringLiteral:
    def __init__(self, val):
        self.V = val

    def traverse(self):
        return z3.StringVal(self.V)

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


class Not:
    def __init__(self, v):
        self.V = v

    def __str__(self):
        return '!{}'.format(self.V)

    def traverse(self):
        return z3.Not(self.V.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __and__(self, other):
        return And(self, other)

    def __inverse__(self, other):
        return Not(self, other)

class Eq:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def __str__(self):
        return '{} == {}'.format(self.L, self.R)

    def traverse(self):
        return self.L.traverse() == self.R.traverse()

    def __or__(self, other):
        return Or(self, other)

    def __and__(self, other):
        return And(self, other)

    def __inverse__(self, other):
        return Not(self, other)

class Or:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def __str__(self):
        return '{} | {}'.format(self.L, self.R)

    def traverse(self):
        return z3.Or(self.L.traverse(), self.R.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __and__(self, other):
        return And(self, other)

    def __inverse__(self, other):
        return Not(self, other)    

class And:
    def __init__(self, l, r):
        self.L = l
        self.R = r

    def __str__(self):
        return '{} | {}'.format(self.L, self.R)

    def traverse(self):
        return z3.And(self.L.traverse(), self.R.traverse())

    def __or__(self, other):
        return Or(self, other)

    def __and__(self, other):
        return And(self, other)    

    def __inverse__(self, other):
        return Not(self, other)    
    

class Predicate:
    def __init__(self, expr):
        self.expr = expr

    def verify(self):
        solver = z3.Solver()
        solver.add(self.expr.traverse())
        if solver.check() == z3.unsat:
            raise ParameterError('our own predicate is unsolvable')

    def check(self, other):
        '''
        Check checks the predicate against another predicate
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

# User-defined models here
class Server:
    '''
    Server is a domain-specific model (e.g. Teleport server)
    '''
    env = String("server.env")

class User:
    '''
    User is a domain specific model (e.g. Teleport user)
    '''
    team = String("user.team")


p = Predicate(
    User.team == "stage"
)

ret = p.check(Predicate(User.team != "stage"))
print(ret)

# predicate is equivalent to itself
print(p.equivalent(p))

# predicate is equivalent to it's redundant version
print(p.equivalent(Predicate((User.team == "stage") | (User.team == "stage"))))

'''
p = Predicate(
    (Server.env == User.team) & User.team != "stage"
)

ret = p.check(Predicate(Server.env == "prod", User.team == "prod"))
print(ret)
'''

'''
pred = (Server.env == User.team)

# user is not defined, the check should fail
p = predicate(pred, Server.env == "stage")
print(p.check())
'''

# Predicate looks like a simple logical expression,
# so no prior Z3 knowledge is required
'''
pred = (Server.env == User.team) | (Server.env == "stage")
pred2 = (Server.env == "stage")

# But it comes with super-powers!
print(equivalent(pred, pred2))

# And just regular checks against random data:
p = predicate(pred, Server.env == "stage")
print(p.check())
print(p.model())

p = predicate(pred, User.team == "prod", Server.env == "prod")
print(p.check())
print(p.model())

p = predicate(pred, User.team == "prod", Server.env == "pro")
print(p.check())

# TODO: how to build an oracle?
'''
