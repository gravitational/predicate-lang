from solver.ast import Duration, StringTuple
from solver.teleport import AccessNode, Node, Options, OptionsSet, Policy, Rules, User, Resource


class Teleport:
    p = Policy(
        name="access2",
        loud=False,
        allow=Rules(
            AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
            Resource(
                (Resource.kind == "node")
                & StringTuple(("list", "read")).contains(Resource.verb)
            ),
        ),
        options=OptionsSet(
            Options((Options.session_ttl < Duration.new(hours=10))),
            Options((Options.locking_mode == "best_effort")),
            Options((Options.ssh.allow_x11_forwarding == True)),
        ),
        deny=Rules(
            AccessNode(
                (AccessNode.login == "mike")
                | (AccessNode.login == "jester")
                | (Node.labels["env"] == "prod")
            ),
        ),
    )

    def test_access(self):
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
