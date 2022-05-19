import z3

ctx = z3.Context()
fac = z3.RecFunction('fac', z3.IntSort(ctx), z3.IntSort(ctx))

n = z3.Int('n', ctx)
z3.RecAddDefinition(fac, n, z3.If(n == 0, 1, n*fac(n-1)))
print(z3.simplify(fac(5)))

s = z3.Solver(ctx=ctx)
s.add(fac(n) < 3)
s.check()
print(s.model().eval(fac(5)))
