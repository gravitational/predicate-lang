from z3 import *

fp = Fixedpoint()
fp.set("fp.engine","datalog")
fp.set("datalog.generate_explanations",True)

s = BitVecSort(3)
user = Function('user', s, BoolSort())
fp.register_relation(user)

alice = BitVecVal(1, s)
fp.fact(user(alice))

print("current set of rules", fp)

print(fp.query(user(alice)), "is alice a user?")
