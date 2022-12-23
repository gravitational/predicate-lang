"""
Sample forbid allow rules
"""
from solver.teleport import AccessNode, User, Rules


no_allow = {
    "no root users": AccessNode(User.name == "root"),
    "buggy1": User.name == "root",
    "buggy2": Rules(User.name == "root"),

}
