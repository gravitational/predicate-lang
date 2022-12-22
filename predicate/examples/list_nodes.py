from solver.ast import StringTuple
from solver.teleport import AccessNode, Policy, Resource, Rules


class Teleport:
    p = Policy(
        name="list_nodes",
        loud=False,
        allow=Rules(
            Resource(
                (Resource.kind == "node")
                & StringTuple(("list", "read")).contains(Resource.verb)
            ),
            AccessNode((AccessNode.login == "root")),
        ),
    )
