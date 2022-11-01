from solver.teleport import Resource, Policy, Rules, Node, User


class Teleport:
    p = Policy(
        name="list_nodes",
        loud=False,
        allow=Rules(
            Resource((Resource.namespace == "default") & (Resource.kind == "node")),
            Node((Node.login == "root"))
        ),
    )
