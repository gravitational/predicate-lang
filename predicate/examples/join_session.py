from solver.teleport import JoinSession, Policy, Rules, User
from solver.ast import Predicate


class Teleport:
    p = Policy(
        name="join_session",
        loud=False,
        allow=Rules(
            # Equivalent to `join_sessions`:
            # https://goteleport.com/docs/access-controls/guides/moderated-sessions/#join_sessions
            JoinSession(
                (JoinSession.count == 1) &
                ((JoinSession.mode == "peer") | (JoinSession.mode == "observer")) &
                (JoinSession.on_leave == "pause")
            ),
        ),
    )

    def test_access(self):
        ret, _ = self.p.check(
            JoinSession(
                (JoinSession.count == 1) &
                (JoinSession.mode == "observer") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is True, "any single user (with this policy) can join a session as an observer"

        ret, _ = self.p.check(
            JoinSession(
                (JoinSession.count == 1) &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is False, "any single user (with this policy) cannot join a session as a moderator"
