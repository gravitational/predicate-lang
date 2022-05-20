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

class Server:
    env = String("env")

class User:
    team = String("team")

def predicate(*expr):
    solver = z3.Solver()
    for e in expr:
        solver.add(e.traverse())
    return solver

pred = (Server.env == User.team) | (Server.env == "stage")

p = predicate(pred, Server.env == "stage")
print(p.check())
print(p.model())

p = predicate(pred, User.team == "prod", Server.env == "prod")
print(p.check())
print(p.model())
