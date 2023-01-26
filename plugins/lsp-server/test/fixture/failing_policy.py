# pylint: skip-file
from solver.teleport import AccessNode, Policy, Rules, User


class Teleport:
    p = Policy(
        name="access",
        allow=Rules(
            AccessNode(User.name == "root")
        )
    )
