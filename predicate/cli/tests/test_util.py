import os

from ..util import create_dir_if_not_exist, create_policy_from_template, parse_classname, normalize_policy_name

TEST_DIR_PATH = "testpath"
TEST_POLICY = "devOps"


def test_create_dir_if_not_exist():
    create_dir_if_not_exist(TEST_DIR_PATH)
    assert (os.path.exists(TEST_DIR_PATH)) is True
    os.rmdir(TEST_DIR_PATH)


# We should ideally test for if the template creates a valid python file.
# But since the template creates a commented code for now, I think we can simple test if the
# template produces desired variable names
def test_create_policy_from_template():
    """
    For policy name 'developer", the class name should be "Developer, name should be "developer"
    and the test function should be "test_developer". 
    """
    sample = """
from solver.teleport import AccessNode, Options, OptionsSet, Policy, Rules

class Developer:
    p = Policy(
        name= "developer",
        loud=False,
        allow=Rules(AccessNode()),
        options=OptionsSet(Options()),
        deny=Rules( AccessNode()),
    )

    def test_developer(self):
        # Test allowed policy 
        # ret, _ = self.p.check(AccessNode())
        # assert ret is True, "developer can login to specified node"

        # Test denied policy 
        # ret, _ = self.p.check(AccessNode())
        # assert ret is False, "developer should not login to specified node"
    """
    policy_name = "developer"
    policy = create_policy_from_template(policy_name)
    assert (sample.strip() == policy.strip()) is True


def test_parse_classname():
    policy1 = """
from solver.ast import Duration
from solver.teleport import AccessNode, Node, Options, OptionsSet, Policy, Rules, User


class Developer:
    p = Policy(
        name="developer",
        loud=False,
        allow=Rules(
            AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
        ),
        options=OptionsSet(Options((Options.max_session_ttl < Duration.new(hours=10)))),
        deny=Rules(
            AccessNode(
                (AccessNode.login == "mike")
                | (AccessNode.login == "jester")
                | (Node.labels["env"] == "prod")
            ),
        ),
    )

    def test_developer(self):
        # Alice will be able to login to any machine as herself
        ret, _ = self.p.check(
            AccessNode(
                (AccessNode.login == "alice")
                & (User.name == "alice")
                & (Node.labels["env"] == "dev")
            )
        )
        assert ret is True, "Alice can login with her user to any node"

        # No one is permitted to login as mike
        ret, _ = self.p.query(AccessNode((AccessNode.login == "mike")))
        assert ret is False, "This role does not allow access as mike"

        # No one is permitted to login as jester
        ret, _ = self.p.query(AccessNode((AccessNode.login == "jester")))
        assert ret is False, "This role does not allow access as jester"

        """

    class_name = parse_classname(policy1)
    assert (class_name == "Developer") is True


def test_normalize_policy_name():
    name = " test policy_name-test"

    class_name = normalize_policy_name(name, "class")
    file_name = normalize_policy_name(name, "file")

    assert (class_name == "TestPolicyNameTest") & (file_name == "test_policy_name_test") is True
