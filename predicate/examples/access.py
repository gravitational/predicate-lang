from solver.ast import Duration
from solver.teleport import (
    AccessNode,
    Node,
    Option,
    Options,
    Policy,
    Rules,
    User,
)


class Teleport:
    p = Policy(
        name="access",
        loud=True,
        options=Options(
            Option.session_ttl <= Duration.new(hours=10),
            Option.session_recording_mode <= "strict",
            Option.allow_agent_forwarding == True,
        ),
        allow=Rules(
            AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
        ),
        deny=Rules(
            AccessNode(
                (AccessNode.login == "mike")
                | (AccessNode.login == "jester")
                | (Node.labels["env"] == "prod")
            ),
        ),
    )

    def test_access(self):
        # Alice will be able to login as herself to env=dev machines
        ret = self.p.check(
            AccessNode(
                (AccessNode.login == "alice")
                & (User.name == "alice")
                & (Node.labels["env"] == "dev")
            ),
            Options(
                Option.session_ttl <= Duration.new(hours=10),
                Option.session_recording_mode <= "strict",
                Option.allow_agent_forwarding == True,
            ),
        )
        assert ret.solves is True, "This policy allows access to env=dev machines as alice"

        # No one is permitted to login as mike
        ret = self.p.query(
            AccessNode(
                (AccessNode.login == "mike")
            )
        )
        assert ret.solves is False, "This policy does not allow access as mike"

        # No one is permitted to access env=prod machines
        ret = self.p.query(
            AccessNode(
                (Node.labels["env"] == "prod")
            )
        )
        assert ret.solves is False, "This policy does not allow access to env=prod machines"

        # Alice is permitted to login as herself
        ret = self.p.query(
            AccessNode(
                (AccessNode.login == "alice")
            )
        )
        assert ret.solves is True, "This policy allows access as alice"

        # Alice is not permitted to login as herself without strict session recording
        ret = self.p.query(
            AccessNode(
                (AccessNode.login == "alice")
            ),
            Options(
                Option.session_recording_mode <= "best_effort"
            )
        )
        assert ret.solves is False, "This policy does not allows access as alice without strict session recording"