import z3

solver = z3.Solver()

env = z3.Function('env', z3.StringSort(), z3.StringSort())
role1 = z3.And(
    z3.Contains(env(z3.StringVal("env")), z3.StringVal("prod")),
    z3.Not(z3.Contains(env(z3.StringVal("env")), z3.StringVal("tion"))),
)

solver.add(role1)
solver.add(env(z3.StringVal("env")) != z3.StringVal("prod"))

result = solver.check()
if z3.sat == result:
  print(solver.model())
else:
  print('No solution!')
