from lint.rule import NoAllow, get_rules
import yaml
from lint.constants import RuleCategory
from solver.teleport import AccessNode, User
from runpy import run_path


RULE_PATH = "lint/tests/mock_rules.py"
INVALID_RULE_PATH = "lint/tests/mock_invalid_rule_file.py"

RULE_NAME = "no_allow"


def test_NoAllow():

    module = run_path(RULE_PATH)
    rules = module[RuleCategory.NO_ALLOW]

    test_policy = AccessNode(User.name == "root")
    # test if invalid predicates are caught
    assert test_policy
    valid = NoAllow().check(rules['rule1'], test_policy)
    invalid = NoAllow().check(rules['rule2'], test_policy)
    assert valid is True & invalid is False


def test_get_rules():
    module = get_rules(RULE_PATH, RULE_NAME)
    assert module is not None

    module = get_rules(INVALID_RULE_PATH, RULE_NAME)
    assert module is None
