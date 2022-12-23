from lint.rule import NoAllow, get_rules
from solver.teleport import AccessNode, User
from runpy import run_path
from pytest import raises
from solver.errors import ParameterError

def test_NoAllow():

    module = run_path("lint/tests/mock_ast_rule.py")
    rules = module["Developer"].p
    test_policy = AccessNode(
        ((AccessNode.login == User.name) & (User.name != "root"))
        | (User.traits["team"] == ("admins",))
    )

    passing = NoAllow().check(rules, test_policy)
    assert passing is True


def test_get_rules():
    rules = get_rules("lint/tests/mock_lint_rule_file.py", "no_allow")

    assert (len(rules) == 3) is True
