import z3

solver = z3.Solver()

user_country = z3.String("user_country")
node_location = z3.String("node_location")
node_running = z3.String("node_running")

role1 = z3.And(user_country == node_location, node_running == z3.StringVal("fooapp"))
role2 = z3.And(user_country != node_location, node_running == z3.StringVal("fooapp"))

solver.add(z3.Distinct(role1, role2))
result = solver.check()
if z3.sat == result:
    print(solver.model())
else:
    print("No solution!")

solver = z3.Solver()
solver.add(role1)
solver.add(user_country == "Canada")
solver.add(node_location == "Canada")
solver.add(node_running == "fooapp")
result = solver.check()
if z3.sat == result:
    print("Allowed")
else:
    print("Denied")
