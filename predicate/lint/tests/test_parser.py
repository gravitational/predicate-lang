from lint.parser import AllowVisitor, get_ast_tree, get_rules


LINENO = 20
END_LINENO = 25


def test_AllowVisitor():
    class_name = "Developer"
    with open('lint/tests/data/policy.py', 'r') as file:
        data = file.read()
        tree = get_ast_tree(data)
        visitor = AllowVisitor(class_name)
        visitor.visit(tree)
        lineno, end_lineno = visitor.lineno, visitor.end_lineno
        print(lineno, end_lineno)
        assert (lineno == LINENO) & (end_lineno == END_LINENO)


def test_get_rules():
    rules = get_rules("lint/tests/data/no_allow.py", "no_allow")
    assert len(rules) == 5
