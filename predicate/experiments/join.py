import z3

traits = z3.Function("traits", z3.StringSort(), z3.StringSort())
x = z3.String("x")

s = z3.Solver()
s.add(traits(x) == z3.StringVal("potato"))
s.add(traits(z3.StringVal("alice")) == z3.StringVal("potato"))
s.add(x == z3.StringVal("alice"))
print(s.check())


s = z3.Solver()
s.add(traits(x) == z3.StringVal("sre"))
s.add(traits(z3.StringVal("alice")) == z3.StringVal("dev"))
s.add(x == z3.StringVal("alice"))
print(s.check())
