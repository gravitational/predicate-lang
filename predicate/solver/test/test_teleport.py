import pytest

from .. import (
    Case,
    Default,
    Duration,
    ParameterError,
    Predicate,
    Select,
    StringLiteral,
    StringSetMap,
)
from ..teleport import (
    LoginRule,
    User,
    Node,
    AccessNode,
    Options,
    OptionsSet,
    Policy,
    PolicyMap,
    PolicySet,
    Rules,
    JoinSession,
    Session,
    map_policies,
    try_login,
)


class TestTeleport:
    def test_node(self):
        p = Policy(
            name="test",
            allow=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
        )
        assert ret is True, "check works on a superset"

    def test_allow_policy_set(self):
        a = Policy(
            name="a",
            allow=Rules(
                AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod")),
            ),
        )

        b = Policy(
            name="b",
            allow=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "stage")),
            ),
        )

        s = PolicySet([a, b])
        ret, _ = s.check(
            AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod"))
        )
        assert ret is True, "check works on a subset"

        ret, _ = s.check(AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "stage")))
        assert ret is True, "check works on a subset"

        ret, _ = s.check(AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")))
        assert ret is False, "rejects the merge"

    def test_deny_policy_set(self):
        a = Policy(
            name="a",
            allow=Rules(
                AccessNode(
                    ((AccessNode.login == "root") & (Node.labels["env"] == "prod"))
                    | ((AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod"))
                )
            ),
        )

        b = Policy(
            name="b",
            deny=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        s = PolicySet([a, b])
        ret, _ = s.check(AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")))
        assert ret is False, "deny in a set overrides allow"

        ret, _ = s.check(
            AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod"))
        )
        assert ret is True, "non-denied part of allow is OK"

    def test_valid_options(self):
        # check that only < inequalities are possible
        _ = Options(Options.max_session_ttl < Duration.new(hours=3))
        _ = Options(Duration.new(hours=3) > Options.max_session_ttl)

        with pytest.raises(Exception):
            _ = Options(Options.max_session_ttl > Duration.new(hours=3))
        with pytest.raises(Exception):
            _ = Options(Duration.new(hours=3) < Options.max_session_ttl)

        with pytest.raises(Exception):
            _ = Options(Options.max_session_ttl == Duration.new(hours=3))
        with pytest.raises(Exception):
            _ = Options(Duration.new(hours=3) == Options.max_session_ttl)

        with pytest.raises(Exception):
            _ = Options(Options.max_session_ttl != Duration.new(hours=3))
        with pytest.raises(Exception):
            _ = Options(Duration.new(hours=3) != Options.max_session_ttl)

    def test_options(self):
        p = Policy(
            name="b",
            options=OptionsSet(
                Options(
                    (Options.max_session_ttl < Duration.new(hours=10))
                    & (Options.max_session_ttl < Duration.new(seconds=10)),
                )
            ),
            allow=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            # Since we only have <, it's impossible to specify a `session_ttl` that would not be valid.
            # This means that the predicate will always match the policy.
            & Options(Options.max_session_ttl < Duration.new(hours=3))
        )

        assert ret is True, "options and core predicate matches"

    def test_options_extra(self):
        """
        Tests that predicate works when options expression is superset
        """
        p = Policy(
            name="p",
            options=OptionsSet(
                Options(
                    (Options.max_session_ttl < Duration.new(hours=10))
                ),
                Options(Options.pin_source_ip == True),
            ),
            allow=Rules(
                # unrelated rules are with comma, related rules are part of the predicate
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            & Options(
                (Options.max_session_ttl < Duration.new(hours=3))
                # TODO: `check` doesn't require that `pin_source_ip` is defined here, but should!?.
                & (Options.pin_source_ip == True)
            )
        )

        assert ret is True, "options and core predicate matches"

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            & Options(
                (Options.max_session_ttl < Duration.new(hours=3))
                & (Options.pin_source_ip == False)
            )
        )
        assert ret is False, "options fails restriction when contradiction is specified"

    def test_options_policy_set(self):
        a = Policy(
            name="a",
            options=OptionsSet(
                Options(
                    (Options.max_session_ttl < Duration.new(hours=10))
                ),
                Options(Options.pin_source_ip == True),
            ),
            allow=Rules(
                AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "stage")),
            ),
        )

        b = Policy(
            name="b",
            allow=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        p = PolicySet([a, b])

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            & Options(
                (Options.max_session_ttl < Duration.new(hours=3))
                & (Options.pin_source_ip == True)
            )
        )

        assert ret is True, "options and core predicate matches"

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            & Options(
                (Options.max_session_ttl < Duration.new(hours=3))
                & (Options.pin_source_ip == False)
            )
        )

        assert ret is False, "options fails restriction"

    def test_options_policy_set_enum(self):
        # policy a requires best effort
        a = Policy(
            name="a",
            options=OptionsSet(
                Options(
                    (Options.recording_mode > "best_effort")
                    | (Options.recording_mode == "best_effort")
                ),
            ),
            allow=Rules(
                AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "stage")),
            ),
        )

        # policy b requires strict recording mode
        b = Policy(
            name="b",
            options=OptionsSet(
                Options(Options.recording_mode == "strict"),
            ),
            allow=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        p = PolicySet([a, b])

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            & Options(Options.recording_mode == "strict")
        )

        assert ret is True, "options and core predicate matches"

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
            & Options(Options.recording_mode == "best_effort")
        )

        assert (
            ret is False
        ), "options fails recording mode restriction from the policy b"

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "ubuntu")
                & (Node.labels["env"] == "stage")
                & (Node.labels["os"] == "Linux")
            )
            & Options(Options.recording_mode == "strict")
        )

        assert ret is True, "options and core predicate matches"

        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "ubuntu")
                & (Node.labels["env"] == "stage")
                & (Node.labels["os"] == "Linux")
            )
            & Options(Options.recording_mode == "best_effort")
        )

        assert (
            ret is False
        ), "strict is enforced for all modes of access across all policies in the set"

    def test_join_session(self):
        p = Policy(
            name="join_session",
            allow=Rules(
                JoinSession(
                    (User.traits["team"].contains("dev")) &
                    ((JoinSession.mode == "observer") | (JoinSession.mode == "peer")) &
                    ((Session.owner.traits["team"].contains("dev")) | (Session.owner.traits["team"].contains("intern")))
                ),
            ),
            deny=Rules(
                JoinSession(
                    User.traits["team"].contains("intern")
                )
            )
        )

        ret, _ = p.check(
            JoinSession(
                (User.traits["team"] == ("dev",)) &
                (JoinSession.mode == "observer") &
                (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert ret is True, "a dev user can join a session from an intern user as an observer"

        ret, _ = p.check(
            JoinSession(
                (User.traits["team"] == ("marketing",)) &
                (JoinSession.mode == "observer") &
                (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert ret is False, "a marketing user cannot join a session from an intern user as an observer"

        ret, _ = p.check(
            JoinSession(
                (User.traits["team"] == ("dev",)) &
                (JoinSession.mode == "moderator") &
                (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert ret is False, "a dev user cannot join a session from an intern user as a moderator"

        ret, _ = p.check(
            JoinSession(
                (User.traits["team"] == ("dev", "intern")) &
                (JoinSession.mode == "observer") &
                (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert ret is False, "a dev intern user cannot join a session from an intern user as an observer"

    def test_login_rules(self):
        """
        Test login rules test simple login rule
        """
        external = StringSetMap("external")
        traits = LoginRule(
            "traits",
            {
                "login": external["email"].replace("@", "-"),
            },
        )
        p = Predicate(
            (external["email"] == ("alice@wonderland.local",))
            & (traits["login"] == ("alice-wonderland.local",))
        )
        ret, _ = p.solve()
        assert ret is True, "transformation has been applied"

    def test_policy_wrong_expr(self):
        """
        Test that policy mapping always returns the right value
        """
        with pytest.raises(ParameterError) as exc:
            PolicyMap(
                Select(
                    # Default is necessary to specify default empty sequence or type
                    Default(StringLiteral("test")),
                )
            )
        assert "should eval to string list" in str(exc.value)

        with pytest.raises(ParameterError) as exc:
            external = StringSetMap("external")
            PolicyMap(
                Select(
                    Case(
                        external["groups"].contains_regex("admin-.*"),
                        external["groups"],
                    ),
                    # Default is necessary to specify default empty sequence or type
                    Default(StringLiteral("test")),
                )
            )

    def test_policy_mapping(self):
        """
        Test policy mapping
        """
        external = StringSetMap("external")

        s = PolicyMap(
            Select(
                Case(
                    external["groups"].contains_regex("admin-.*"),
                    external["groups"].replace("admin-", "ext-"),
                ),
                # Default is necessary to specify default empty sequence or type
                Default(external["groups"]),
            )
        )

        ret, _ = Predicate(
            (s == ("ext-test", "ext-prod"))
            & (external["groups"] == ("admin-test", "admin-prod"))
        ).solve()
        assert ret is True, "match and replace works"

        ret, _ = Predicate(
            (s == ("dev-test", "dev-prod"))
            & (external["groups"] == ("dev-test", "dev-prod"))
        ).solve()
        assert ret is True, "match and replace works default value"

    def test_full_cycle(self):
        external = StringSetMap("external")
        traits = LoginRule(
            "traits",
            {
                "login": external["email"].replace("@", "-"),
                # copy over external groups
                "groups": external["groups"],
            },
        )
        p = Predicate(
            (external["email"] == ("alice@wonderland.local",))
            & (traits["login"] == ("alice-wonderland.local",))
        )
        ret, _ = p.solve()
        assert ret is True, "match and replace works in login rules"

        s = PolicyMap(
            Select(
                Case(
                    external["groups"].contains_regex("admin-.*"),
                    external["groups"].replace("admin-", "ext-"),
                ),
                # Default is necessary to specify default empty sequence or type
                Default(external["groups"]),
            )
        )

        ret, _ = Predicate(
            (s == ("ext-test", "ext-prod"))
            & (external["groups"] == ("admin-test", "admin-prod"))
        ).solve()
        assert ret is True, "match and replace works in policy maps"

        ret, _ = Predicate(
            (s == ("dev-test", "dev-prod"))
            & (external["groups"] == ("dev-test", "dev-prod"))
        ).solve()
        assert ret is True, "match and replace works in policy maps (default value)"

        # dev policy allows access to stage, and denies access to root
        dev = Policy(
            name="dev-stage",
            allow=Rules(
                AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "stage")),
            ),
            deny=Rules(
                AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")),
            ),
        )

        # ext policy allows access to prod as ubuntu,
        # but requires strict recording mode
        ext = Policy(
            name="ext-stage",
            options=OptionsSet(
                Options(Options.recording_mode == "strict"),
            ),
            allow=Rules(
                AccessNode(
                    (AccessNode.login == traits["login"].first())
                    & (Node.labels["env"] == "prod")
                ),
            ),
        )

        p = PolicySet([dev, ext])

        # make sure that policy set will never allow access to prod
        ret, _ = p.check(AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod")))
        assert ret is False

        policy_names = try_login(
            s,
            (external["email"] == ("alice@wonderland.local",))
            & (external["groups"] == ("ext-stage",)),
        )
        assert policy_names == set(("ext-stage",))
        p = map_policies(policy_names, (dev, ext))

        # policy set will allow Alice to connect to prod if her
        # email is alice@wonderland.local
        ret, _ = p.check(
            AccessNode(
                (AccessNode.login == "alice-wonderland.local")
                & (Node.labels["env"] == "prod")
            )
        )
        assert ret is True

        # TODO: How to simplify testing and make it shorter?
        # TODO: How to connect policy mappings and
