from lint.rule import NoAllow
from solver.teleport import AccessNode, User
from runpy import run_path


def test_NoAllow():

    module = run_path("lint/tests/data/policy_sample/policy.py")
    rules = module["Developer"].p
    test_policy = AccessNode(
        ((AccessNode.login == User.name) & (User.name != "beta"))
        | (User.traits["team"] == ("alpha",))
    )

    passing = NoAllow().check(rules, test_policy)
    assert passing is True
