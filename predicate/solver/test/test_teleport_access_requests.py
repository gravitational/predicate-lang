from ..teleport import (
    Policy,
    Request,
    RequestPolicy,
    Review,
    Rules,
    Thresholds,
)

from ..ast import StringList, If


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
                    ((RequestPolicy.names == ('access-stage',)) & (RequestPolicy.approvals["access-stage"].len() > 1) & (RequestPolicy.denials["access-stage"].len() < 1))
                ),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )

        # Can devs request access to stage?
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ('access-stage',)) & (RequestPolicy.approvals['access-stage'].len() > 0)
            )
        )
        assert ret is True, "Devs can request access to stage"

        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ('access-prod',)) & (RequestPolicy.approvals['access-prod'].len() > 0)
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

        # Can user with these policies review a role?
        ret, _ = devs.query(
            Review(
                RequestPolicy.names.contains(
                    "access-prod",
                )
            )
        )
        assert ret is False, "can't review role that is not listed in the policy"

        # TODO: how to bind to roles?
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ('access-stage',)) &
                (RequestPolicy.approvals['access-stage'] == ('alice', 'bob'))
            )
        )
        assert ret is True, "two folks have approved the request"

        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ('access-stage',)) &
                (RequestPolicy.approvals['access-stage'] == ('alice', 'bob')) &
                (RequestPolicy.denials['access-stage'] == ('ketanji',))
            )
        )
        assert ret is False, "two folks have approved the request, but one person denied it"

        # Model the approve / request scenario using if/else and list
        # Work in progress
        #
        devs = Policy(
            name="devs",
            allow=Rules(
                Request(
                    ((RequestPolicy.names == ('access-stage',)) & (RequestPolicy.approvals["access-stage"].len() > 0) & (RequestPolicy.denials["access-stage"].len() < 1))
                ),
                Review(RequestPolicy.names == ("access-stage",)),
            ),
        )
        approvals = StringList("approvals")
        ret, _ = devs.query(
            Request(
                (RequestPolicy.names == ('access-stage',)) &
                (RequestPolicy.approvals['access-stage'] == If(devs.build_predicate(
                    Request(RequestPolicy.names == ('access-stage',))
                ).expr, approvals.add("approval"), StringList("approvals", ())))
            )
        )
        assert ret is True, "two folks have approved the request"

