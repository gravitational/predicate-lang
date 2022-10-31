from solver.ast import Duration
from solver.teleport import Node, Options, OptionsSet, Policy, Rules, User


class Teleport:
    p = Policy(
        name="list_nodes",
        loud=False,
        allow=Rules(
            Node((Node.namespace == "default")),
        ),
    )
