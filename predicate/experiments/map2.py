import z3

# taken from
# https://ericpony.github.io/z3py-tutorial/advanced-examples.htm
StringList = z3.Datatype("List")
StringList.declare("cons", ("car", z3.StringSort()), ("cdr", StringList))
# nil list
StringList.declare("nil")
# Create the datatype
StringList = StringList.create()
# cons, car and cdr are function declarations, and nil a constant
cons = StringList.cons
car = StringList.car
cdr = StringList.cdr
nil = StringList.nil

l1 = cons(z3.StringVal("apple"), cons(z3.StringVal("potato"), nil))
l2 = cons(z3.StringVal("apple"), cons(z3.StringVal("potato"), nil))

fn = z3.Function("fn", z3.StringSort(), StringList)
fn_contains = z3.RecFunction("contains", StringList, z3.StringSort(), z3.BoolSort())


def define_contains():
    vals = z3.Const("vals", StringList)
    element = z3.StringVal("search")
    z3.RecAddDefinition(
        fn_contains,
        [vals, element],
        z3.If(
            nil == vals,
            z3.BoolVal(False),
            z3.If(
                car(vals) == element, z3.BoolVal(True), fn_contains(cdr(vals), element)
            ),
        ),
    )


define_contains()

s = z3.Solver()
s.add(fn(z3.StringVal("key")) == l1)
s.add(fn(z3.StringVal("key")) == l2)
s.add(fn_contains(l1, z3.StringVal("apple")) == z3.BoolVal(True))
s.add(fn_contains(l1, z3.StringVal("banana")) == z3.BoolVal(True))

ret = s.check()
print("Ret: {}".format(ret))

"""
fn_a = z3.Function('fn_a', z3.StringSort(), z3.StringSort(), z3.BoolSort())
s.add(fn_a(z3.StringVal("key"), z3.StringVal("potato"))  == True)
fn_b = z3.RecFunction('fn_b', z3.StringSort(), z3.StringSort(), z3.BoolSort())
key = z3.String('key')
val = z3.String('val')
z3.RecAddDefinition(fn_b, [key, val],
                    z3.If(z3.And(key == z3.StringVal("key"), val == z3.StringVal("potato")),
                          z3.BoolVal(True),
                          z3.If(z3.And(key == z3.StringVal("key"), val == z3.StringVal("apple")),
                                z3.BoolVal(True),
                                z3.BoolVal(False))))
s.add(fn_b(z3.StringVal("key"), z3.StringVal("strawberry"))  == True)
#free = z3.String('free')
#s.add(z3.Distinct(fn_a(z3.StringVal("key"), free), fn_b(z3.StringVal("key"), free)))
ret = s.check()
print("Ret: {}".format(ret))
"""
