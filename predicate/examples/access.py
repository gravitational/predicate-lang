class Teleport:
    p = Policy(
        name="access",
        loud=False,
        allow=Rules(
            Node(
                ((Node.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
        ),
        options=OptionsSet(Options((Options.max_session_ttl < Duration.new(hours=10)))),
        deny=Rules(
            Node(
                (Node.login == "mike")
                | (Node.login == "jester")
                | (Node.labels["env"] == "prod")
            ),
        ),
    )

    def test_access(self):
        # Alice will be able to login to any machine as herself
        ret, _ = self.p.check(
            Node(
                (Node.login == "alice")
                & (User.name == "alice")
                & (Node.labels["env"] == "dev")
            )
        )
        assert ret is True, "Alice can login with her user to any node"

        # No one is permitted to login as mike
        ret, _ = self.p.query(Node((Node.login == "mike")))
        assert ret is False, "This role does not allow access as mike"

        # No one is permitted to login as jester
        ret, _ = self.p.query(Node((Node.login == "jester")))
        assert ret is False, "This role does not allow access as jester"
