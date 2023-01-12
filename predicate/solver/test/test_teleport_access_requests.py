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
        # Any denial invalidates the request.
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        (RequestPolicy.names == ("access-stage",))
                        & (
                            RequestPolicy.names.for_each(
                                lambda x: RequestPolicy.approvals[x].len() > 1
                            )
                        )
                        & (
                            RequestPolicy.names.for_each(
                                lambda x: RequestPolicy.denials[x].len() < 1
                            )
                        )
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
                # Notice we are using full approval definition here using == to other map
                & (
                    RequestPolicy.approvals
                    == StringSetMap("reviews", {"access-stage": ("alice", "bob")})
                )
            )
        )
        assert ret is True, "two folks have approved the request"

        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                # Notice we are using full approval definition here using == to other map
                & (
                    RequestPolicy.approvals
                    == StringSetMap("reviews", {"access-stage": ("alice",)})
                )
            )
        )
        assert ret is False, "only one person has approved the request"

        # TODO: it's easy to make a mistake and have the same name for StringSetMap
        # * Create unique anonymous maps as a quick solution
        # * Check for name collisions to avoid hard to debug bugs in the future.
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (
                    RequestPolicy.approvals
                    == StringSetMap("approvals", {"access-stage": ("alice", "bob")})
                )
                & (
                    RequestPolicy.denials
                    == StringSetMap("denials", {"access-stage": ("ketanji",)})
                )
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
                Request(RequestPolicy.names == ("access-stage",)),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        request = RequestPolicy.names == ("access-stage",)

        # First, verify that success is possible.
        ret, _ = devs.query(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap("approvals", {"access-stage": ("alice", "bob")})
                )
            )
        )
        assert ret is True, "request approved"

        ret, _ = devs.query(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap("approvals", {"access-stage": ()})
                )
            )
        )
        assert (
            ret is False
        ), "request is missing implicit minimum required approvers count"

        ret, _ = devs.query(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap("approvals", {"access-stage": ("bob", "ketanji")})
                )
                & (
                    RequestPolicy.denials
                    == StringSetMap("denials", {"access-stage": ("alice",)})
                )
            )
        )
        assert (
            ret is False
        ), "one person denied, access request is denied due to implicit deny default"

        # the policy below has error in the sign that makes it unsolvable
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
                    request
                    & (
                        RequestPolicy.approvals
                        == StringSetMap("approvals", {"access-stage": ()})
                    )
                )
            )
        assert "unsolvable" in str(exc.value)

        # Test defaults with two policies
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

        # First, make sure success is possible
        request = RequestPolicy.names == ("access-stage", "access-prod")
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals",
                        {"access-stage": ("ketanji",), "access-prod": ("alice",)},
                    )
                )
            )
        )
        assert ret is True, "Both polices have been approved"

        request = RequestPolicy.names == ("access-stage", "access-prod")
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals", {"access-stage": ("ketanji",), "access-prod": ()}
                    )
                )
            )
        )
        assert (
            ret is False
        ), "one person have approved the request, but the request fails because both roles have to be approved"

        request = RequestPolicy.names == ("access-stage", "access-prod")
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals",
                        {"access-stage": ("ketanji",), "access-prod": ("alice",)},
                    )
                )
                & (
                    RequestPolicy.denials
                    == StringSetMap("denials", {"access-stage": ("bob",)})
                )
            )
        )
        assert (
            ret is False
        ), "Both polices have been approved, but one person denied one policy"

    def test_access_requests_reviews_function(self):
        """
        Tests review function properties.
        """
        devs = Policy(
            name="devs",
            allow=Rules(
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        # Reviews needs request policy names to be concrete. It will eval RequestPolicy.names and for each one,
        # will try to add a review
        request = Request(RequestPolicy.names.contains("access-stage"))

        assert reviews(
            request,
            ("alice", devs),  # alice reviewed as devs
        ) == {"access-stage": ["alice"]}, "Simple review works"

        request = Request(
            RequestPolicy.names.contains("access-prod")
            & RequestPolicy.names.contains("access-stage")
        )
        assert reviews(request, ("alice", devs),) == {
            "access-stage": ["alice"],
            "access-prod": [],
        }, "Combined review works, but access-prod has no approvers"

        # let's fix policy to allow both stage and prod review
        devs = Policy(
            name="devs",
            allow=Rules(
                Review(
                    RequestPolicy.names.contains("access-stage")
                    | RequestPolicy.names.contains("access-prod")
                ),
            ),
        )
        request = Request(
            RequestPolicy.names
            == (
                "access-stage",
                "access-prod",
            )
        )
        assert reviews(request, ("alice", devs),) == {
            "access-stage": ["alice"],
            "access-prod": ["alice"],
        }, "Combined review works"

    def test_access_requests_reviews(self):
        """
        Model the approve / request scenario using review expression
        """
        # devs can requests to stage, but can't review them
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(RequestPolicy.names == ("access-stage",)),
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
                    RequestPolicy.approvals
                    == StringSetMap("approvals", reviews(request, ("alice", sre)))
                )
            )
        )
        assert ret is True, "one person has approved the request"

        request = RequestPolicy.names == ("access-stage",)
        ret, _ = devs.query(
            Request(
                request
                & (
                    RequestPolicy.denials
                    == StringSetMap("approvals", reviews(request, ("ketanji", sre)))
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
                        & (
                            RequestPolicy.names.for_each(
                                lambda x: RequestPolicy.approvals[x].len() > 1
                            )
                        )
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

        # Test a successfull request
        request = RequestPolicy.names == ("access-stage", "access-prod")
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals",
                        {"access-stage": ("ketanji",), "access-prod": ("alice",)},
                    )
                )
            )
        )
        assert ret is True, "both policies have been requested and approved"

        # With multi-roles, both roles have to be requested
        request = RequestPolicy.names == ("access-stage",)
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals",
                        {"access-stage": ("ketanji",), "access-prod": ("alice",)},
                    )
                )
            )
        )
        assert (
            ret is False
        ), "one person have approved the request, but the request fails because both roles have to be requested"

        request = RequestPolicy.names == ("access-stage", "access-prod")
        ret, _ = devs.check(
            Request(
                request
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals",
                        {"access-stage": ("ketanji",), "access-prod": ("alice",)},
                    )
                )
                & (
                    RequestPolicy.denials
                    == StringSetMap("denials", {"access-stage": ("bob",)})
                )
            )
        )
        assert (
            ret is False
        ), "both policies have been requested and approved, but one person has denied the request"

    def test_access_requests_duplicates(self):
        """
        Makes sure that duplicate reviews are ignored
        """
        # Devs are allowed to request 'access-prod' policy.
        # Two approvals are required to proceed.
        # Any denial invalidates the request.
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    (
                        (RequestPolicy.names == ("access-stage",))
                        # Need at least two denials to deny this access request
                        & (
                            RequestPolicy.names.for_each(
                                lambda x: RequestPolicy.approvals[x].len() > 1
                            )
                        )
                    )
                ),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )
        # Can devs request access to stage?
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (
                    RequestPolicy.approvals
                    == StringSetMap("approvals", {"access-stage": ("ketanji", "alice")})
                )
            )
        )
        assert ret is True, "Two approvals, from different people"

        # Can devs request access to stage?
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ("access-stage",))
                & (
                    RequestPolicy.approvals
                    == StringSetMap(
                        "approvals", {"access-stage": ("ketanji", "ketanji")}
                    )
                )
            )
        )
        assert ret is False, "Two approvals, but from the same person"

    def test_access_requests_todo(self):
        """
        * Model search_as access requests and resource based access requests.
        * Add invariant that users cant review their own requests. To do that add a default that User.name != "self"?
        * Model invariant that a static policy can't be escaped -
        if you got policy "a" and got policy "b" approved, you get both "a" and "b" in policy set
        * Model reviews where reviewer is authorized and reviews
        just a part of access request (partial approval)
        """
