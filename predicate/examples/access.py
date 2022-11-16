from solver.ast import Duration
from solver.teleport import (
    AccessNode,
    Node,
    Options,
    Policy,
    RecordingMode,
    Rules,
    SourceIp,
    User,
)


class Teleport:
    p = Policy(
        name="access",
        loud=False,
        options=Options(
            max_session_ttl=Duration.new(hours=10),
            recording_mode=RecordingMode.STRICT,
            source_ip=SourceIp.PINNED,
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
        # Alice will be able to login to any machine as herself
        ret = self.p.check(
            AccessNode(
                (AccessNode.login == "alice")
                & (User.name == "alice")
                & (Node.labels["env"] == "dev")
            )
        )
        assert ret.solves is True, "Alice can login with her user to any node"

        # No one is permitted to login as mike
        ret = self.p.query(AccessNode((AccessNode.login == "mike")))
        assert ret.solves is False, "This role does not allow access as mike"

        # No one is permitted to login as jester
        ret = self.p.query(AccessNode((AccessNode.login == "jester")))
        assert ret.solves is False, "This role does not allow access as jester"
