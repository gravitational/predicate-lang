import z3
# reference
# https://z3prover.github.io/api/html/namespacez3py.html

class StringLiteral:
    def __init__(self, val):
        self.V = val

    def traverse(self):
        return z3.StringVal(self.V)

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

    def __str__(self):
        return 'String({})'.format(self.name)

    def traverse(self):
        return self.fn(z3.StringVal(self.name))

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

# user model
def predicate(*expr):
    solver = z3.Solver()
    for e in expr:
        solver.add(e.traverse())
    return solver

def equivalent(a, b):
    solver = z3.Solver()
    solver.add(z3.Distinct(a.traverse(), b.traverse()))
    result = solver.check()
    if z3.unsat == result:
        return (True, "Roles are equivalent")
    elif z3.sat == result:
        return (False, f"Roles are not equivalent; counterexample: {solver.model()}")
    else:
        return (False, str(result))

# User-defined model here
    
class Server:
    '''
    Server is a domain-specific model (e.g. Teleport server)
    '''
    env = String("env")

class User:
    '''
    User is a domain specific model (e.g. Teleport user)
    '''
    team = String("team")


# Predicate looks like a simple logical expression,
# so no prior Z3 knowledge is required
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
