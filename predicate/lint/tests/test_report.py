from lint.report import get_code_snippet, Report
from common.constants import RuleCategory

LINENO = 20
END_LINENO = 25

test_snippet = """
allow=Rules(
            AccessNode(
                ((AccessNode.login == User.name) & (User.name != "beta"))
                | (User.traits["team"] == ("alpha",))
            ),
        ),
"""


def test_get_code_snippet():
    with open('lint/tests/data/policy_sample/policy.py', 'r') as file:
        snippet = get_code_snippet(file, LINENO, END_LINENO)
        assert (snippet.strip().replace(" ", "") == test_snippet.strip().replace(" ", ""))


def test_no_allow_report():
    result = Report(
        RuleCategory.NO_ALLOW,
        "test_rule",
        "Teleport",
        {}
    ).get_report("lint/tests/data/policy_sample/access.py")

    assert (result["category"] == RuleCategory.NO_ALLOW)


def test_duplicate_report():
    result = Report(
        RuleCategory.DUPLICATE,
        "test_rule",
        "Teleport",
        {"is_name": True}
    ).get_report("lint/tests/data/policy_sample/access.py")

    assert (result["category"] == RuleCategory.DUPLICATE)
