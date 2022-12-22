from lint.report import get_code_snippet

LINENO = 20
END_LINENO = 25

test_snippet = """
allow=Rules(
            AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
        ),
"""


def test_get_code_snippet():
    with open('lint/tests/mock_ast_test.py', 'r') as file:
        snippet = get_code_snippet(file, LINENO, END_LINENO)
        assert (snippet.strip().replace(" ", "") == test_snippet.strip().replace(" ", "")) is True