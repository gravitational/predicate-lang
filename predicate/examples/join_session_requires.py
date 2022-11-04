from solver.teleport import JoinSession, Policy, Rules, User
from solver.ast import Predicate


class Teleport:
    p = Policy(
        name="join_session_requires",
        loud=False,
        allow=Rules(
            # Equivalent to `require_session_join`:
            # https://goteleport.com/docs/access-controls/guides/moderated-sessions/#require_session_join
            JoinSession(
                (User.traits["team"].contains("admin")) &
                (JoinSession.count == 2) &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "terminate")
            )
        ),
    )

    def test_access(self):
        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("admin",)) &
                (JoinSession.count == 2) &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "terminate")
            )
        )
        assert ret is True, "any two users (with this policy) from the admin team can join a session as moderators"

        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev",)) &
                (JoinSession.count == 2) &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "terminate")
            )
        )
        assert ret is False, "any two users (with this policy) from the dev team cannot join a session as moderators"

        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("admin",)) &
                (JoinSession.count == 1) &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "terminate")
            )
        )
        assert ret is False, "a single user (with this policy) from the admin team cannot join a session as moderators"
