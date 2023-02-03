"""
Sample forbid allow rules
"""
from solver.ast import StringTuple
from solver.teleport import AccessNode, User, JoinSession, Session, Node, Resource


no_allow = {
    "no root users": AccessNode(User.name == "root"),
    "no join session by interns": JoinSession(
        (User.traits["team"].contains("dev"))
        & ((JoinSession.mode == "observer") | (JoinSession.mode == "peer"))
        & (
            (Session.owner.traits["team"].contains("dev"))
            | (Session.owner.traits["team"].contains("intern"))
        )
    ),
    "no wildcard assignment": AccessNode(User.name == "*"),
    "no if user is from admin team": AccessNode(
        ((AccessNode.login == User.name) & (User.name != "root"))
        | (User.traits["team"] == ("admins",))
    ),
    "no dbadmin in prod environment": AccessNode((Node.labels["env"] == "prod") & (User.name == "dbadmin")),
    "no read access on Node resource": Resource(
        (Resource.kind == "node")
        & StringTuple(("list", "read")).contains(Resource.verb)
    )
}
