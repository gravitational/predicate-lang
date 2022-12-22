"""
Sample forbid allow rules
"""

from solver.teleport import AccessNode, User, JoinSession, Session, Node, Rules


no_allow = {
    "no root users": AccessNode(User.name == "root"),
    "no if user is from admin team": AccessNode(
        ((AccessNode.login == User.name) & (User.name != "root"))
        | (User.traits["team"] == ("admins",))
    ),
    "no join session by interns": JoinSession(
        (User.traits["team"].contains("dev"))
        & ((JoinSession.mode == "observer") | (JoinSession.mode == "peer"))
        & (
            (Session.owner.traits["team"].contains("dev"))
            | (Session.owner.traits["team"].contains("intern"))
        )
    ),
    "no wildcard assignment": AccessNode(User.name == "*"),
    "no dbadmin in prod environment": AccessNode((Node.labels["env"] == "prod") & (User.name == "dbadmin"))
}
