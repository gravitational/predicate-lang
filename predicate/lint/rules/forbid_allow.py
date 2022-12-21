"""
Sample forbid allow rules
"""

from solver.teleport import AccessNode, User, JoinSession, Session, Node



forbid_allow_rules = {
    "disallow root users": AccessNode(User.name == "root"),
    "disallow if user is from admin team": AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
    "disallow join by root": JoinSession(
                (User.traits["team"].contains("dev"))
                & ((JoinSession.mode == "observer") | (JoinSession.mode == "peer"))
                & (
                    (Session.owner.traits["team"].contains("dev"))
                    | (Session.owner.traits["team"].contains("intern"))
                )
            ),
    "disallow wildcard assignment": AccessNode(User.name == "*"),
    "disallow dbadmin in prod environment": AccessNode((Node.labels["env"] == "prod") & (User.name == "dbadmin"))
}
