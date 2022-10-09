class Teleport:
    p = Policy(
        name="access",
        loud=False,
        allow=Rules(
            Node((Node.login == User.name) & (User.name == "root")),
        ),
        deny=Rules(
            Node((Node.login == "mike") | (Node.login == "jester")),
        ),
    )

    def test_access(self):
        # Alice will be able to login to any machine as herself
        ret, _ = self.p.check(Node((Node.login == "alice") & (User.name == "alice")))
        assert ret is True, "Alice can login with her user to any node"

        # We can verify that a strong invariant holds:
        # Unless a username is root, a user can not access a server as
        # root. This creates a problem though, can we deny access as root
        # altogether?
        ret, _ = self.p.check(Node((Node.login == "root") & (User.name != "root")))
        assert (
            ret is False
        ), "This role does not allow access as root unless a user name is root"

        # No one is permitted to login as mike
        ret, _ = self.p.query(Node((Node.login == "mike")))
        assert ret is False, "This role does not allow access as mike"

        # No one is permitted to login as jester
        ret, _ = self.p.query(Node((Node.login == "jester")))
        assert ret is False, "This role does not allow access as jester"
