from solver.ast import Duration
from solver.teleport import Node, Options, OptionsSet, Policy, Rules, User


class Teleport:
    p = Policy(
        name="logins",
        loud=False,
        allow=Rules(
            Node(
                (User.name == Node.login) |
                (Node.labels["env"] == "prod")
            ),
        ),
        deny=Rules(
            Node(
                (Node.login == "root")
            )
        )
    )