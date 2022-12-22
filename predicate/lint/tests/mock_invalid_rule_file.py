from solver.teleport import AccessNode, User, JoinSession, Session, Node, Rules

no_allow = {
    "valid_rule": AccessNode(User.name == "root"),
    "invalid_rule": Rules(AccessNode(JoinSession == "root"))
}
