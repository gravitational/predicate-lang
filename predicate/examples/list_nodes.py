from solver.teleport import Resource, Policy, Rules, Node
from solver.ast import StringTuple


class Teleport:
    p = Policy(
        name="list_nodes",
        loud=False,
        allow=Rules(
            Resource((Resource.namespace == "default") & (Resource.kind == "node") & StringTuple(("list", "read")).contains(Resource.verb)),
            Node((Node.login == "root"))
        ),
    )
