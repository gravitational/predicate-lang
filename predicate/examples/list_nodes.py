from solver.ast import StringTuple
from solver.teleport import Node, Policy, Resource, Rules


class Teleport:
    p = Policy(
        name="list_nodes",
        loud=False,
        allow=Rules(
            Resource(
                (Resource.namespace == "default")
                & (Resource.kind == "node")
                & StringTuple(("list", "read")).contains(Resource.verb)
            ),
            Node((Node.login == "root")),
        ),
    )
