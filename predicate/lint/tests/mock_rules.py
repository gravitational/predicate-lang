"""
Sample no_allow rules to test
"""

from solver.teleport import AccessNode, User, JoinSession, Session, Node, Rules


no_allow = {
    "rule1": AccessNode(User.name == "root"),
    "rule2": AccessNode(User.name == "admin"),
}
