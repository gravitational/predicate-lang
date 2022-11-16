from solver.teleport import JoinSession, Policy, Rules, Session, User


class Teleport:
    p = Policy(
        name="join_session",
        loud=False,
        allow=Rules(
            # Equivalent to `join_sessions`:
            # https://goteleport.com/docs/access-controls/guides/moderated-sessions/#join_sessions
            JoinSession(
                (User.traits["team"].contains("dev"))
                & ((JoinSession.mode == "observer") | (JoinSession.mode == "peer"))
                & (
                    (Session.owner.traits["team"].contains("dev"))
                    | (Session.owner.traits["team"].contains("intern"))
                )
            ),
        ),
        deny=Rules(JoinSession(User.traits["team"].contains("intern"))),
    )

    def test_access(self):
        ret = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev",))
                & (JoinSession.mode == "observer")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is True
        ), "a dev user can join a session from an intern user as an observer"

        ret = self.p.check(
            JoinSession(
                (User.traits["team"] == ("marketing",))
                & (JoinSession.mode == "observer")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is False
        ), "a marketing user cannot join a session from an intern user as an observer"

        ret = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev",))
                & (JoinSession.mode == "moderator")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is False
        ), "a dev user cannot join a session from an intern user as a moderator"

        ret = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev", "intern"))
                & (JoinSession.mode == "observer")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is False
        ), "a dev intern user cannot join a session from an intern user as an observer"
