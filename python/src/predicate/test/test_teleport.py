import pytest
from predicate import ast, Predicate, String, StringMap, ParameterError, regex, StringTuple
from predicate.teleport import *

class TestTeleport:
    def test_node(self):
        p = Policy(
            allow=Rules(
                node = Node(
                    (Node.login == "root") & (Node.labels["env"] == "prod")),
            )
        )

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux")))
        assert ret == True, "check works on a superset"

    def test_requests(self):
        # TODO: support builder pattern?
        # p.allow.request.roles = (Role.name == "access-prod")
        # p.allow.request.thresholds = (Thresholds.approve > 1) & (Thresholds.deny < 2)
        # p.allow.review = (Role.name == "access-prod")
        p = Policy(
            allow=Rules(
                # Let's make those predicates too!
                request = Request(
                    (Role.name == "access-prod") & (Thresholds.approve == 1) & (Thresholds.deny == 2)
                ),
                review = Review(Role.name == "access-prod"),
            )
        )

        # Can user request a role?
        ret, _ = p.query(
            Request(
                (Role.name == "access-prod")
            )
        )
        assert ret == True, "check works"

        # Can user with these policies review a role?
        ret, _ = p.query(
            Review(Role.name == "access-prod")
        )
        assert ret == True, "check works"
