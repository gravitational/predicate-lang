from solver.ast import StringTuple, Duration
from solver.teleport import AccessNode, Policy, Resource, Rules, Options, OptionsSet, Node


class Teleport:
    p = Policy(
        name="list_nodes",
        loud=False,
        allow=Rules(
            Resource(
                (Resource.kind == "Kube")
                & StringTuple(("list", "read")).contains(Resource.verb)
            ),
        ),
        options=OptionsSet(
            Options((Options.session_ttl < Duration.new(hours=10))),
            Options((Options.locking_mode == "best_effort")),
            Options((Options.ssh.allow_x11_forwarding == True)),
        ),
        deny=Rules(
            AccessNode(
                (AccessNode.login == "mike")
                | (AccessNode.login == "jester")
                | (Node.labels["env"] == "prod")
            ),
        ),
    )
