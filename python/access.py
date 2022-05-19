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

class Labels:
    env = String("env")

def predicate(expr):
    print(expr)
    solver = z3.Solver()
    solver.add(expr.traverse())
    print(solver.check())
    return solver

pred = predicate((Labels.env == "prod") | (Labels.env == "stage"))
print(pred.model())
pred.add(Labels.env.fn(z3.StringVal(Labels.env.name)) == z3.StringVal("stage"))
print(pred.check())

