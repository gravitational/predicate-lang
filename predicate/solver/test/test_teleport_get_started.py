from ..teleport import Node, Policy, Rules, User


class TestTeleportGetStarted:
    """
    This test suite demonstrates teleport getting started experience
    """

    def test_node_access(self):
        """
        Let's write a simple policy and test it.
        """
        p = Policy(
            name="everyone",
            allow=Rules(
                Node((Node.login == "root")),
            ),
        )

        # Check if alice can access nodes as root
        ret, _ = p.check(Node((Node.login == "root") & (User.name == "alice")))
        assert ret is True, "everyone can access as root, including alice"

        # This is not a very useful policy, because it gives everyone
        # access as root. Let's narrow down this policy to let users
        # only access as their own logins
        p = Policy(
            name="everyone",
            allow=Rules(
                Node((Node.login == User.name)),
            ),
        )

        # Alice will be able to login to any machine as herself
        ret, _ = p.check(Node((Node.login == "alice") & (User.name == "alice")))
        assert ret is True, "Alice can login with her user to any node"

        # We can verify that a strong invariant holds:
        # Unless a username is root, a user can not access a server as
        # root. This creates a problem though, can we deny access as root
        # altogether?
        ret, _ = p.check(Node((Node.login == "root") & (User.name != "root")))
        assert (
            ret is False
        ), "This role does not allow access as root unless a user name is root"

        # Let's prohibit root access altogether. Deny rules always take
        # precendence over any allow rules.
        p = Policy(
            name="everyone",
            allow=Rules(
                Node(Node.login == User.name),
            ),
            deny=Rules(Node(Node.login == "root")),
        )

        # Notice the difference between check and query. Query allows to query
        # partial condititions, our predicate requires user to be specified,
        # while this query does not specify any user. Checks require all
        # parameters of the predicate, while queries do not.
        ret, _ = p.query(Node((Node.login == "root")))
        assert ret is False, "This role does not allow access as root to anyone"

    def test_node_access_multiple_teams(self):
        """
        Let's write a couple of policies for different
        teams and see how they work together.
        """

        # Let's imagine two teams - devs and db-admins.
        # We would like to allow devs to access machines
        # of their own team and db-admins to do the same for DBs they manage.

        devs_and_admins = Policy(
            name="devs-and-db-admins",
            allow=Rules(
                Node(
                    (Node.login == User.name)
                    & User.traits["team"].contains(Node.labels["team"])
                ),
            ),
        )

        # Check if alice can access nodes as root
        ret, _ = devs_and_admins.check(
            Node(
                (User.name == "alice")
                & (User.traits["team"] == ("dev",))
                & (Node.login == "alice")
                & (Node.labels["team"] == "dev")
            )
        )
        assert (
            ret is True
        ), "Policy lets Alice to access nodes as her username if nodes are labeled with dev"

        # Check if bob can access nodes as root
        ret, _ = devs_and_admins.check(
            Node(
                (User.name == "bob")
                & (User.traits["team"] == ("db-admins",))
                & (Node.login == "bob")
                & (Node.labels["team"] == "db-admins")
            )
        )
        assert (
            ret is True
        ), "Policy lets Bob to access nodes as her username if nodes are labeled with dev"

        # The policy
