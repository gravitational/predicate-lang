import pytest

from ..ast import ParameterError, StringSetMap
from ..teleport import Node, Policy, Request, RequestPolicy, Review, Rules, reviews


class TestTeleportAccessRequests:
    """
    This test suite covers and explains access requests feature set.
    """

    def test_access_requests_single(self):
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
                        & (RequestPolicy.approvals.for_each_key().len() > 1)
                        & (RequestPolicy.denials.for_each_key().len() < 1)
                    )
                ),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        # Can devs request access to stage?
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
            )
        )
        assert ret is True, "Devs can request access to stage"

        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-prod",))
                & (RequestPolicy.approvals["access-prod"].len() > 0)
            )
        )
        assert ret is False, "Devs can't request access to prod"

        # Can devs review access to prod?
        ret, _ = devs.query(
            Review(
                RequestPolicy.names.contains(
                    "access-stage",
                )
            )
        )
        assert ret is True, "Devs can review other folks access to stage"

        # Can user with these policies review a policy?
        ret, _ = devs.query(
            Review(
                RequestPolicy.names.contains(
                    "access-prod",
                )
            )
        )
        assert ret is False, "can't review policy that is not listed in the policy"

        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"] == ("alice", "bob"))
            )
        )
        assert ret is True, "two folks have approved the request"

        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"] == ("alice", "bob"))
                & (RequestPolicy.denials["access-stage"] == ("ketanji",))
            )
        )
        assert (
            ret is False
        ), "two folks have approved the request, but one person denied it"

    def test_access_requests_defaults(self):
        """
        Tests that at least one approval by default is required to proceed.
        """
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(((RequestPolicy.names == ("access-stage",)))),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        request = RequestPolicy.names == ("access-stage",)
        ret, _ = devs.query(
            Request(request & (RequestPolicy.approvals["access-stage"] == reviews()))
        )
        assert ret is False, "misses implicit minimum required approver"

        ret, _ = devs.query(
            Request(
                request
                & (RequestPolicy.approvals["access-stage"] == reviews((devs, request)))
                & (RequestPolicy.denials["access-stage"] == reviews((devs, request)))
            )
        )
        assert (
            ret is False
        ), "one person denied, access request is denied due to implicit deny default"

        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        (RequestPolicy.names == ("access-stage",))
                        & (
                            RequestPolicy.approvals["access-stage"].len() < 0
                        )  # error in the sign
                    )
                ),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        with pytest.raises(ParameterError) as exc:
            request = RequestPolicy.names == ("access-stage",)
            ret, _ = devs.query(
                Request(
                    request & (RequestPolicy.approvals["access-stage"] == reviews())
                )
            )
        assert "unsolvable" in str(exc.value)

        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        # When there are two policies in the list, both
                        # have to pass their thresholds to be approved,
                        # and any policy denied will result in denial for all
                        (RequestPolicy.names == ("access-stage", "access-prod"))
                    )
                ),
                Review(
                    (RequestPolicy.names == ("access-stage",))
                    | (RequestPolicy.names == ("access-prod",))
                ),
            ),
        )

        request = RequestPolicy.names == ("access-stage", "access-prod")
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals["access-stage"]
                    == reviews((devs, Request(request)))
                )
            )
        )
        assert (
            ret is False
        ), "one person have approved the request, but the request fails because both roles have to be approved"

    def test_access_requests_review_expression(self):
        """
        Model the approve / request scenario using review expression
        """
        # devs can requests to stage, but can't review them
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(((RequestPolicy.names == ("access-stage",)))),
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
        ret, _ = devs.query(
            Request(
                request
                & (
                    RequestPolicy.approvals["access-stage"]
                    == reviews((sre, Request(request)))
                )
            )
        )
        assert ret is True, "one person has approved the request"

        request = RequestPolicy.names == ("access-stage",)
        ret, _ = devs.query(
            Request(
                request
                & (
                    RequestPolicy.denials["access-stage"]
                    == reviews((sre, Request(request)))
                ),
            )
        )
        assert ret is False, "one person has denied the request"

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
                        & (RequestPolicy.approvals.for_each_key().len() > 1)
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
        ret, _ = devs.check(
            Review(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
                & (external["groups"] == ("sre",))
                & (Node.labels["env"] == "sre")
            )
        )
        assert ret is True, "Devs can request access to stage for nodes in their env"

        # Can devs review access to stage?
        ret, _ = devs.check(
            Review(
                (RequestPolicy.names == ("access-stage",))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
                & (external["groups"] == ("sre",))
                & (Node.labels["env"] == "prod")
            )
        )
        assert (
            ret is False
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
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names.contains("access-stage"))
                & (RequestPolicy.approvals["access-stage"].len() > 0)
            )
        )
        assert ret is True, "Devs can request access to stage"

        # Can devs request access to stage and prod at the same time?
        ret, _ = devs.query(
            Request((RequestPolicy.names == ("access-stage", "access-prod")))
        )
        assert ret is True, "Devs can request access to stage and prod"

        # With multi-roles, both roles have to be requested
        request = RequestPolicy.names == ("access-stage",)
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals["access-stage"]
                    == reviews((sre, Request(request)))
                )
            )
        )
        assert (
            ret is False
        ), "one person have approved the request, but the request fails because both roles have to be requested"

        # Request for two policies got approved
        ret, model = devs.check(
            Request(
                (RequestPolicy.names == ("access-stage", "access-prod"))
                & (
                    # one approval for prod
                    RequestPolicy.approvals["access-prod"]
                    == reviews(
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
            ret is True
        ), "request is approved with two approvals for prod and one for stage"

        # Request for two policies got approved, but one person has denied the request
        ret, model = devs.check(
            Request(
                (RequestPolicy.names == ("access-stage", "access-prod"))
                & (
                    # one approval for prod
                    RequestPolicy.approvals["access-prod"]
                    == reviews(
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
                & (
                    # one denial for prod
                    RequestPolicy.denials["access-prod"]
                    == reviews(
                        (sre, Request(RequestPolicy.names.contains("access-prod")))
                    )
                )
            )
        )
        assert ret is False, "request is denied regardless of any extra approvals"

    def test_access_requests_todo(self):
        """
        * Check that default denials < 1 is not added if other expression is specified
        * Add more tests with access request failures.
        * How to distinguish query when people forgot to add reviews vs legitimate query?
        * Model search_as access requests and resource based access requests.
        * Add invariant that users cant review their own requests.
        * Model invariant that a static policy can't be escaped -
        if you got policy "a" and got policy "b" approved, you get both "a" and "b" in policy set
        * Model reviews where reviewer is authorized and reviews
        just a part of access request (partial approval)
        """
