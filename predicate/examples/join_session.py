from solver.teleport import JoinSession, Policy, Rules, User, Node


class Teleport:
    p = Policy(
        name="join_session",
        loud=False,
        allow=Rules(
            # Equivalent to `join_sessions`:
            # https://goteleport.com/docs/access-controls/guides/moderated-sessions/#join_sessions
            JoinSession(
                (User.traits["team"].contains("dev")) &
                (Node.labels["env"] == "dev") &
                ((JoinSession.mode == "peer") | (JoinSession.mode == "observer")) &
                (JoinSession.on_leave == "pause")
            ),
        ),
        deny=Rules(
            JoinSession(
                User.traits["team"].contains("intern")
            )
        )
    )

    def test_access(self):
        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev",)) &
                (Node.labels["env"] == "dev") &
                (JoinSession.mode == "observer") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is True, "a user from the dev team can join an env=dev node session as an observer"

        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("marketing",)) &
                (Node.labels["env"] == "dev") &
                (JoinSession.mode == "observer") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is False, "a user from the marketing team cannot join an env=dev node session as an observer"

        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev",)) &
                (Node.labels["env"] == "prod") &
                (JoinSession.mode == "observer") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is False, "a user from the dev team cannot join an env=prod node session as an observer"

        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev",)) &
                (Node.labels["env"] == "dev") &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is False, "a user from the dev team cannot join an env=dev node session as a moderator"

        ret, _ = self.p.check(
            JoinSession(
                (User.traits["team"] == ("dev", "intern")) &
                (Node.labels["env"] == "dev") &
                (JoinSession.mode == "moderator") &
                (JoinSession.on_leave == "pause")
            )
        )
        assert ret is False, "an intern from the dev team cannot join an env=dev node session as an observer"