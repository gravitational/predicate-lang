import pytest
from predicate import ast, Predicate, String, StringMap, ParameterError, regex, StringTuple, Duration
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

    def test_allow_policy_set(self):
        a = Policy(
            allow=Rules(
                node = Node(
                    (Node.login == "ubuntu") & (Node.labels["env"] == "prod")),
            )
        )

        b = Policy(
            allow=Rules(
                node = Node(
                    (Node.login == "root") & (Node.labels["env"] == "stage")),
            )
        )        

        s = PolicySet([a, b])
        ret, _ = s.check(
            Node((Node.login == "ubuntu") & (Node.labels["env"] == "prod")))
        assert ret == True, "check works on a subset"

        ret, _ = s.check(
            Node((Node.login == "root") & (Node.labels["env"] == "stage")))
        assert ret == True, "check works on a subset"

        ret, _ = s.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod")))
        assert ret == False, "rejects the merge"

    def test_deny_policy_set(self):
        a = Policy(
            allow=Rules(
                node = Node(
                    ((Node.login == "root") & (Node.labels["env"] == "prod")) |
                    ((Node.login == "ubuntu") & (Node.labels["env"] == "prod")))))

        b = Policy(
            deny=Rules(
                node = Node(
                    (Node.login == "root") & (Node.labels["env"] == "prod")),
            )
        )        

        s = PolicySet([a, b])
        ret, _ = s.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod")))
        assert ret == False, "deny in a set overrides allow"

        ret, _ = s.check(
            Node((Node.login == "ubuntu") & (Node.labels["env"] == "prod")))
        assert ret == True, "non-denied part of allow is OK"        

        
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

        # Can user with these policies review a role?
        ret, _ = p.query(
            Review(Role.name == "access-stage")
        )
        assert ret == False, "can't approve role that is not listed in the policy"


    def test_options(self):
        p = Policy(
            options = Options(
                (Options.max_session_ttl < Duration.new(hours=10)) &
                (Options.max_session_ttl > Duration.new(seconds=10)),
            ),
            allow=Rules(
                node = Node(
                    (Node.login == "root") & (Node.labels["env"] == "prod")),
            )
        )

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux"))
            &
            Options(Options.max_session_ttl == Duration.new(hours=3))
        )

        assert ret == True, "options and core predicate matches"

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux"))
            &
            Options(Options.max_session_ttl == Duration.new(hours = 50))
        )

        assert ret == False, "options expression fails the entire predicate"


    def test_options_extra(self):
        '''
        Tests that predicate works when options expression is superset
        '''
        p = Policy(
            options = Options(
                (Options.max_session_ttl < Duration.new(hours=10)) &
                (Options.max_session_ttl > Duration.new(seconds=10)) &
                (Options.pin_source_ip == True),
            ),
            allow=Rules(
                node = Node(
                    (Node.login == "root") & (Node.labels["env"] == "prod")),
            )
        )

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux"))
            &
            Options((Options.max_session_ttl == Duration.new(hours=3))
            )
        )

        assert ret == True, "options and core predicate matches"

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux"))
            &
            Options((Options.max_session_ttl == Duration.new(hours=3)) & (Options.pin_source_ip == False)
            )
        )

        assert ret == True, "options fails restriction"


    def test_options_policy_set(self):
        a = Policy(
            options = Options(
                (Options.max_session_ttl < Duration.new(hours=10)) &
                (Options.max_session_ttl > Duration.new(seconds=10)) &
                (Options.pin_source_ip == True),
            ),
            allow=Rules(
                node = Node(
                    (Node.login == "ubuntu") & (Node.labels["env"] == "stage")),
            )            
        )

        b = Policy(
            allow=Rules(
                node = Node(
                    (Node.login == "root") & (Node.labels["env"] == "prod")),
            )
        )

        p = PolicySet([a, b])

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux"))
            &
            Options((Options.max_session_ttl == Duration.new(hours=3))
                    # here, the option does not necessarily apply to this check,
                    # but our check function is strict
            )
        )

        assert ret == True, "options and core predicate matches"

        ret, _ = p.check(
            Node((Node.login == "root") & (Node.labels["env"] == "prod") & (Node.labels["os"] == "Linux"))
            &
            Options((Options.max_session_ttl == Duration.new(hours=3)) & (Options.pin_source_ip == False)
            )
        )

        assert ret == True, "options fails restriction"

