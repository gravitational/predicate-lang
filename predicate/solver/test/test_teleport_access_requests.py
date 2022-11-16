from ..ast import StringSetMap
from ..teleport import Node, Policy, Request, RequestPolicy, Review, Rules, reviews


class TestTeleportAccessRequests:
    """
    This test suite covers and explains access requests feature set.
    """

    def test_access_requests(self):
        """
        Access requests lets users to request access to resources - policies
        and nodes they don't have. Other team members review or deny access
        requests, and policies specifies who can review, how many approvals
        and denies are required.
        """
        # Devs are allowed to request 'access-prod' policy.
        # Two approvals are required to proceed.
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        (RequestPolicy.names == ("access-stage",))
                        & (RequestPolicy.approvals["access-stage"].len() > 1)
                        & (RequestPolicy.denials["access-stage"].len() < 1)
                    )
                ),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        # Can devs request access to stage?
        ret = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
            )
        )
        assert ret.solves is True, "Devs can request access to stage"

        ret = devs.query(
            Request(
                (RequestPolicy.names == ("access-prod",))
                & (RequestPolicy.approvals["access-prod"].len() > 0)
            )
        )
        assert ret.solves is False, "Devs can't request access to prod"

        # Can devs review access to prod?
        ret = devs.query(
            Review(
                RequestPolicy.names.contains(
                    "access-stage",
                )
            )
        )
        assert ret.solves is True, "Devs can review other folks access to stage"

        # Can user with these policies review a role?
        ret = devs.query(
            Review(
                RequestPolicy.names.contains(
                    "access-prod",
                )
            )
        )
        assert ret.solves is False, "can't review role that is not listed in the policy"

        # TODO: how to bind to roles?
        ret = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"] == ("alice", "bob"))
            )
        )
        assert ret.solves is True, "two folks have approved the request"

        ret = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"] == ("alice", "bob"))
                & (RequestPolicy.denials["access-stage"] == ("ketanji",))
            )
        )
        assert (
            ret.solves is False
        ), "two folks have approved the request, but one person denied it"

    def test_access_requests_review_expression(self):
        """
        Model the approve / request scenario using review expression
        """
        # devs can requests to stage, but can't review them
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        (RequestPolicy.names == ("access-stage",))
                        & (RequestPolicy.approvals["access-stage"].len() > 0)
                        & (RequestPolicy.denials["access-stage"].len() < 1)
                    )
                ),
            ),
        )

        # sre's can review requests to stage, but can't request them
        sre = Policy(
            name="sre",
            allow=Rules(
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        request = RequestPolicy.names == ("access-stage",)
        ret = devs.query(
            Request(
                request
                & (
                    RequestPolicy.approvals["access-stage"]
                    == reviews((sre, Request(request)))
                )
            )
        )
        assert ret.solves is True, "one person have approved the request"

        request = RequestPolicy.names == ("access-stage",)
        ret = devs.query(
            Request(
                request
                & (
                    RequestPolicy.denials["access-stage"]
                    == reviews((sre, Request(request)))
                ),
            )
        )
        assert ret.solves is False, "one person has denied the request"

    def test_access_requests_review_limits(self):
        """
        Review limits places limits on what type
        of access request policies users can review.
        """
        # Devs are allowed to request 'access-prod' policy.
        # Two approvals are required to proceed.
        external = StringSetMap("external")
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        (RequestPolicy.names == ("access-stage",))
                        & (RequestPolicy.approvals["access-stage"].len() > 1)
                        & (RequestPolicy.denials["access-stage"].len() < 1)
                    )
                ),
                Review(
                    # devs can review access stage policies, but
                    # only for nodes labeled with their their team
                    (RequestPolicy.names == ("access-stage",))
                    & external["groups"].contains(Node.labels["env"])
                ),
            ),
        )

        # Can devs review access to stage?
        ret = devs.check(
            Review(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
                & (external["groups"] == ("sre",))
                & (Node.labels["env"] == "sre")
            )
        )
        assert (
            ret.solves is True
        ), "Devs can request access to stage for nodes in their env"

        # Can devs review access to stage?
        ret = devs.check(
            Review(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
                & (external["groups"] == ("sre",))
                & (Node.labels["env"] == "prod")
            )
        )
        assert (
            ret.solves is False
        ), "Devs can't request access to stage for nodes not in their env"

    def test_access_requests_multi(self):
        """
        Access requests lets users to request access to resources - policies
        and nodes they don't have. Other team members review or deny access
        requests, and policies specifies who can review, how many approvals
        and denies are required.
        """
        # Devs are allowed to request 'access-prod' policy.
        # Two approvals are required to proceed.
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        # When there are two policies in the list, both
                        # have to pass their thresholds to be approved,
                        # and any policy denied will result in denial for all
                        (RequestPolicy.names == ("access-stage", "access-prod"))
                        # At least one approval for stage
                        & (RequestPolicy.approvals["access-stage"].len() > 0)
                        & (RequestPolicy.denials["access-stage"].len() < 1)
                        # At least two approvals for prod
                        & (RequestPolicy.approvals["access-prod"].len() > 1)
                        & (RequestPolicy.denials["access-prod"].len() < 1)
                    )
                ),
            ),
        )

        # allow reviewing access-stage or access-prod
        sre = Policy(
            name="sre",
            allow=Rules(
                Review(
                    RequestPolicy.names.contains("access-stage")
                    | RequestPolicy.names.contains("access-prod")
                ),
            ),
        )

        # Can devs request access to stage?
        ret = devs.query(
            Request(
                (RequestPolicy.names.contains("access-stage"))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
            )
        )
        assert ret.solves is True, "Devs can request access to stage"

        # Can devs request access to stage and prod at the same time?
        ret = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage", "access-prod"))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
            )
        )
        assert ret.solves is True, "Devs can request access to stage and prod"

        # With multi-roles, both roles have to be requested
        request = RequestPolicy.names == ("access-stage",)
        ret = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals["access-stage"]
                    == reviews((sre, Request(request)))
                )
            )
        )
        assert (
            ret.solves is False
        ), "one person have approved the request, but the request fails because both roles have to be requested"

        # Request for two policies got approved
        ret = devs.check(
            Request(
                (RequestPolicy.names == ("access-stage", "access-prod"))
                & (
                    # two approvals for prod
                    RequestPolicy.approvals["access-prod"]
                    == reviews(
                        (sre, Request(RequestPolicy.names.contains("access-prod"))),
                        (sre, Request(RequestPolicy.names.contains("access-prod"))),
                    )
                )
                & (
                    # one approval for staging
                    RequestPolicy.approvals["access-stage"]
                    == reviews(
                        (sre, Request(RequestPolicy.names.contains("access-stage")))
                    )
                )
            )
        )
        assert (
            ret.solves is True
        ), "request is approved with two approvals for prod and one for stage"

    def test_access_requests_todo(self):
        """
        * More tests with access request failures?
        * How to model search_as access requests properly?
        * How to test that users cant review own requests.
        * Static role can't be escaped - if you got role "a" and got role "b"
        approved, you get both "a" and "b" in policy set
        * The access requests syntax is a bit clumsy
        * What happens if you miss thresholds?
        * Implement permission boundaries (AWS-style)
        """
