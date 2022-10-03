from ..teleport import Policy, Request, RequestPolicy, Review, Rules, Thresholds, replay_request


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
                    (RequestPolicy.names == ("access-prod", "access-stage"))
                    & (Thresholds.approve == 2)
                    & (Thresholds.deny == 1)
                ),
                Review(RequestPolicy.names == ("access-prod",)),
            ),
        )

        # Can devs request access to prod?
        ret, _ = devs.query(Request(RequestPolicy.names.contains("access-prod",)))
        assert ret is True, "Devs can request access to prod"

        # Can devs review access to prod?
        ret, _ = devs.query(Review(RequestPolicy.names.contains("access-prod",)))
        assert ret is True, "Devs can review other folks access to prod"

        # Can user with these policies review a role?
        ret, _ = devs.query(Review(RequestPolicy.names.contains("access-stage",)))
        assert ret is False, "can't review role that is not listed in the policy"

        # TODO finish this
        return
        ret = replay_request(
            request=(devs, Request(RequestPolicy.names.contains("access-prod",))),
            approve=(devs, devs),
            deny=(devs,),
        )
        assert ret is True
