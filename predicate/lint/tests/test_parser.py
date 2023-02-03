from lint.parser import AllowVisitor, DuplicateVisitor, get_ast_tree


def test_AllowVisitor():
    class_name = "Developer"
    with open('lint/tests/data/policy_sample/policy.py', 'r') as file:
        LINENO = 20
        END_LINENO = 25
        data = file.read()
        tree = get_ast_tree(data)
        visitor = AllowVisitor(class_name)
        visitor.visit(tree)
        lineno, end_lineno = visitor.lineno, visitor.end_lineno
        assert (lineno == LINENO) & (end_lineno == END_LINENO)


def test_DuplicateVisitorName():
    class_name = "Developer"
    with open('lint/tests/data/policy_sample/policy.py', 'r') as file:
        LINENO = 18
        END_LINENO = 18
        data = file.read()
        tree = get_ast_tree(data)
        visitor = DuplicateVisitor(class_name,  {"is_name": True})
        visitor.visit(tree)
        lineno, end_lineno = visitor.lineno, visitor.end_lineno
        print(lineno, end_lineno)
        assert (lineno == LINENO) & (end_lineno == END_LINENO)


def test_DuplicateVisitorRule():
    class_name = "Developer"
    with open('lint/tests/data/policy_sample/policy.py', 'r') as file:
        LINENO = 20
        END_LINENO = 33
        data = file.read()
        tree = get_ast_tree(data)
        visitor = DuplicateVisitor(class_name,  {"is_name": False})
        visitor.visit(tree)
        lineno, end_lineno = visitor.lineno, visitor.end_lineno
        print(lineno, end_lineno)
        assert (lineno == LINENO) & (end_lineno == END_LINENO)
