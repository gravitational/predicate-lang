from pathlib import Path
import shutil

from cli.policy_utils import create_policy_from_template, get_policy, normalize_policy_name, create_policy_file
from solver.teleport import Policy, Rules

def test_create_policy_file():
    policy_name = " test file_name-master Dev master "
    final_name = normalize_policy_name(policy_name, "")
    create_policy_file(policy_name, "policytestdir")
    assert (Path(f"policytestdir/{final_name}.py").exists()) is True
    shutil.rmtree("policytestdir")


# We should ideally test for if the template creates a valid python file.
# But since the template creates a commented code for now, I think we can simple test if the
# template produces desired variable names
def test_create_policy_from_template():
    """
    For policy name 'developer", the class name should be "Developer, name should be "developer"
    and the test function should be "test_developer". 
    """
    sample = """
from solver.teleport import Policy, AccessNode, User, Rules

class Developer:
    p = Policy(
        name= "developer",
        loud=False,
        allow=Rules(AccessNode((AccessNode.login == "developer"))),
        # options=OptionsSet(Options()),
        # deny=Rules(AccessNode()),
    )

    def test_developer(self):
        # Test allowed policy 
        ret, _ = self.p.check(AccessNode(AccessNode.login == "developer"))
        assert ret is True, "developer can login to specified node"

        # Test denied policy 
        # ret, _ = self.p.check(AccessNode())
        # assert ret is False, "developer should not login to specified node"

    """
    policy_name = "developer"
    policy = create_policy_from_template(policy_name)
    assert (sample.strip() == policy.strip()) is True


def test_get_policy():
    class_name, policy = get_policy("cli/tests/mock_policy.py")
    assert (class_name == "Developer") & isinstance(policy, Policy) is True



def test_normalize_policy_name():
    name = " test policy_name-test"

    class_name = normalize_policy_name(name, "class")
    file_name = normalize_policy_name(name, "file")

    assert (class_name == "TestPolicyNameTest") & (file_name == "test_policy_name_test") is True
