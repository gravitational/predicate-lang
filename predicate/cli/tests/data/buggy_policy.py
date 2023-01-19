from solver.ast import Duration
from solver.teleport import AccessNode, Node, Options, OptionsSet, Policy, Rules, User, JoinSession


class Developer:
    p = Policy(
        name="developer",
        loud=False,
        allow=Rules(
            AccessNode(
                ((AccessNode.login == "testuser") & (User.name != "testuser"))
                | (User.traits["team"] == ("testteam",))
            ),
            Rules(
                ((AccessNode.login == "testuser") & (User.name != "testuser"))
                | (JoinSession.mode == "observer") == ("testteam",))
        ),
        options=OptionsSet(Options((Options.session_ttl < Duration.new(hours=10)))),
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
