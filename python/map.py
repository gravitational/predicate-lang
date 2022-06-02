import z3

fac = z3.RecFunction('fac', z3.IntSort(), z3.IntSort())
n = z3.Int('n')
z3.RecAddDefinition(fac, n, z3.If(n == 0, 1, n*fac(n-1)))
z3.simplify(fac(5))

s = z3.Solver()
s.add(fac(n) < 3)
print(s.check())
print(s.model().eval(fac(5)))


mapfn = z3.RecFunction('map', z3.StringSort(), z3.StringSort())
x = z3.String("x")

z3.RecAddDefinition(
  mapfn,
  x,
  z3.If(
    x == z3.StringVal("in"),
    z3.StringVal("out"),
    z3.If(
      x == z3.StringVal("in2"),
      z3.StringVal("out2"),
      z3.StringVal(""),
    )
  ))

s = z3.Solver()
s.add(z3.And(mapfn(x) == z3.StringVal("out2"), x == z3.StringVal("in2")))
print(s.check())
print(s.model())

s = z3.Solver()
s.add(z3.And(mapfn(x) != z3.StringVal("")))
print(s.check())
print(s.model().eval(mapfn(z3.StringVal("in"))))
print(s.model().eval(mapfn(z3.StringVal("in2"))))
