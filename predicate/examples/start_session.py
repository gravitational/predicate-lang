from solver.teleport import StartSession, Policy, Rules, User


class Teleport:
    p = Policy(
        name="start_session",
        loud=False,
        allow=Rules(
            # Equivalent to `require_session_join`:
            # https://goteleport.com/docs/access-controls/guides/moderated-sessions/#require_session_join
            StartSession(
                (User.traits["team"].contains("admin")) &
                (StartSession.count == 2) &
                (StartSession.mode == "moderator") &
                (StartSession.on_leave == "terminate")
            )
        ),
    )

    def test_access(self):
        ret, _ = self.p.check(
            StartSession(
                (User.traits["team"] == ("admin",)) &
                (StartSession.count == 2) &
                (StartSession.mode == "moderator") &
                (StartSession.on_leave == "terminate")
            )
        )
        assert ret is True, "any two users from the admin team can start a session as moderators"

        ret, _ = self.p.check(
            StartSession(
                (User.traits["team"] == ("dev",)) &
                (StartSession.count == 2) &
                (StartSession.mode == "moderator") &
                (StartSession.on_leave == "terminate")
            )
        )
        assert ret is False, "any two users from the dev team cannot start a session as moderators"

        ret, _ = self.p.check(
            StartSession(
                (User.traits["team"] == ("admin",)) &
                (StartSession.count == 1) &
                (StartSession.mode == "moderator") &
                (StartSession.on_leave == "terminate")
            )
        )
        assert ret is False, "a single user from the admin team cannot start a session as moderators"
