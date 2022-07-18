import z3

mapfn = z3.Function('map', z3.StringSort(), z3.StringSort())
x = z3.String("x")
y = z3.String("y")

s = z3.Solver()
s.add(mapfn(z3.StringVal("in1")) == z3.StringVal("out1"))
print(s.check())
print(s.model())
s.add(mapfn(z3.StringVal("in2")) == z3.StringVal("out2"))
print(s.check())
print(s.model())

