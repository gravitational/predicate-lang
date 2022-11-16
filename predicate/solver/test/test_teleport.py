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
    AccessNode,
    JoinSession,
    LoginRule,
    Node,
    Options,
    Policy,
    PolicyMap,
    PolicySet,
    RecordingMode,
    Rules,
    Session,
    SourceIp,
    User,
    map_policies,
    try_login,
)


class TestTeleport:
    def test_node(self):
        p = Policy(
            name="test",
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        ret = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
        )
        assert ret.solves is True, "check works on a superset"

    def test_allow_policy_set(self):
        a = Policy(
            name="a",
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        b = Policy(
            name="b",
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "stage")
                ),
            ),
        )

        s = PolicySet([a, b])
        ret = s.check(
            AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod"))
        )
        assert ret.solves is True, "check works on a subset"

        ret = s.check(
            AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "stage"))
        )
        assert ret.solves is True, "check works on a subset"

        ret = s.check(
            AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod"))
        )
        assert ret.solves is False, "rejects the merge"

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
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        s = PolicySet([a, b])
        ret = s.check(
            AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod"))
        )
        assert ret.solves is False, "deny in a set overrides allow"

        ret = s.check(
            AccessNode((AccessNode.login == "ubuntu") & (Node.labels["env"] == "prod"))
        )
        assert ret.solves is True, "non-denied part of allow is OK"

    def test_empty_policy(self):
        with pytest.raises(ParameterError, match="policy name cannot be empty"):
            _ = Policy(name="")

        with pytest.raises(
            ParameterError,
            match="policy must contain either options, allow or deny rules",
        ):
            _ = Policy(name="a")

        with pytest.raises(
            ParameterError,
            match="policy must contain either options, allow or deny rules",
        ):
            _ = Policy(name="a", options=Options(), allow=Rules(), deny=Rules())

        # policy only with options is valid
        _ = Policy(name="a", options=Options(max_session_ttl=Duration.new(hours=10)))

        # policy only with allow rules is valid
        _ = Policy(name="a", allow=Rules(AccessNode(AccessNode.login == "root")))

        # policy only with deny rules is valid
        _ = Policy(name="a", deny=Rules(AccessNode(AccessNode.login == "root")))

    def test_empty_rules(self):
        assert Rules().empty() is True, "empty rules are empty"
        assert (
            Rules(AccessNode(AccessNode.login == "root")).empty() is False
        ), "non empty rules are non empty"

    def test_empty_options(self):
        assert Options().empty() is True, "empty options are empty"
        assert (
            Options(max_session_ttl=Duration.new(hours=10)).empty() is False
        ), "non empty options are non empty"

        assert Rules().empty() is True, "empty rules are empty"
        assert (
            Rules(AccessNode(AccessNode.login == "root")).empty() is False
        ), "non empty rules are non empty"

    def test_options_init(self):
        # TODO add tests ensuring that users cannot set invalid option values
        # for example, the next test should fail and doesn't
        _ = Options(
            max_session_ttl=Duration.new(hours=10),
            recording_mode=Duration.new(hours=10),
            source_ip=Node.labels["env"] == "prod",
        )

    def test_options_combine(self):
        result = Options.combine(
            Options(),
            Options(),
        )
        assert result.max_session_ttl is None
        assert result.source_ip is None
        assert result.recording_mode is None

        result = Options.combine(
            Options(max_session_ttl=Duration.new(hours=10)),
            Options(),
        )
        assert result.max_session_ttl == Duration.new(hours=10)
        assert result.source_ip is None
        assert result.recording_mode is None

        result = Options.combine(
            Options(),
            Options(max_session_ttl=Duration.new(hours=3)),
        )
        assert result.max_session_ttl == Duration.new(hours=3)
        assert result.source_ip is None
        assert result.recording_mode is None

        result = Options.combine(
            Options(max_session_ttl=Duration.new(hours=10)),
            Options(max_session_ttl=Duration.new(hours=3)),
        )
        assert result.max_session_ttl == Duration.new(hours=3)
        assert result.source_ip is None
        assert result.recording_mode is None

        result = Options.combine(
            Options(max_session_ttl=Duration.new(hours=3)),
            Options(max_session_ttl=Duration.new(hours=10)),
        )
        assert result.max_session_ttl == Duration.new(hours=3)
        assert result.source_ip is None
        assert result.recording_mode is None

        result = Options.combine(
            Options(source_ip=SourceIp.PINNED),
            Options(source_ip=SourceIp.UNPINNED),
        )
        assert result.max_session_ttl is None
        assert result.source_ip == SourceIp.PINNED
        assert result.recording_mode is None

        result = Options.combine(
            Options(source_ip=SourceIp.UNPINNED),
            Options(source_ip=SourceIp.PINNED),
        )
        assert result.max_session_ttl is None
        assert result.source_ip == SourceIp.PINNED
        assert result.recording_mode is None

        result = Options.combine(
            Options(recording_mode=RecordingMode.BEST_EFFORT),
            Options(recording_mode=RecordingMode.STRICT),
        )
        assert result.max_session_ttl is None
        assert result.source_ip is None
        assert result.recording_mode == RecordingMode.STRICT

        result = Options.combine(
            Options(recording_mode=RecordingMode.STRICT),
            Options(recording_mode=RecordingMode.BEST_EFFORT),
        )
        assert result.max_session_ttl is None
        assert result.source_ip is None
        assert result.recording_mode == RecordingMode.STRICT

    def test_options(self):
        p = Policy(
            name="b",
            options=Options(
                max_session_ttl=Duration.new(hours=10),
            ),
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        ret = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
        )
        assert ret.solves is True, "options and core predicate matches"
        assert ret.options.max_session_ttl == Duration.new(hours=10)

    def test_options_extra(self):
        """
        Tests that predicate works when options expression is superset
        """
        p = Policy(
            name="p",
            options=Options(
                max_session_ttl=Duration.new(hours=10),
                source_ip=SourceIp.PINNED,
            ),
            allow=Rules(
                # unrelated rules are with comma, related rules are part of the predicate
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        ret = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
        )

        assert ret.solves is True
        assert ret.options.max_session_ttl == Duration.new(hours=10)
        assert ret.options.source_ip == SourceIp.PINNED

    def test_options_policy_set(self):
        a = Policy(
            name="a",
            options=Options(
                max_session_ttl=Duration.new(hours=10),
                source_ip=SourceIp.PINNED,
                recording_mode=RecordingMode.BEST_EFFORT,
            ),
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "ubuntu") & (Node.labels["env"] == "stage")
                )
            ),
        )

        b = Policy(
            name="b",
            options=Options(
                max_session_ttl=Duration.new(hours=3),
                source_ip=SourceIp.UNPINNED,
                recording_mode=RecordingMode.STRICT,
            ),
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        p = PolicySet([a, b])

        ret = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
        )

        assert ret.solves is True, "options and core predicate matches"
        assert ret.options.max_session_ttl == Duration.new(hours=3)
        assert ret.options.source_ip == SourceIp.PINNED
        assert ret.options.recording_mode == RecordingMode.STRICT

    def test_options_policy_set_enum(self):
        # policy a requires best effort
        a = Policy(
            name="a",
            options=Options(
                recording_mode=RecordingMode.BEST_EFFORT,
            ),
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "ubuntu") & (Node.labels["env"] == "stage")
                ),
            ),
        )

        # policy b requires strict recording mode
        b = Policy(
            name="b",
            options=Options(
                recording_mode=RecordingMode.STRICT,
            ),
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        p = PolicySet([a, b])

        ret = p.check(
            AccessNode(
                (AccessNode.login == "root")
                & (Node.labels["env"] == "prod")
                & (Node.labels["os"] == "Linux")
            )
        )

        assert ret.solves is True, "options and core predicate matches"
        assert ret.options.recording_mode == RecordingMode.STRICT

        ret = p.check(
            AccessNode(
                (AccessNode.login == "ubuntu")
                & (Node.labels["env"] == "stage")
                & (Node.labels["os"] == "Linux")
            )
        )

        assert ret.solves is True, "options and core predicate matches"
        assert ret.options.recording_mode == RecordingMode.STRICT

    def test_join_session(self):
        p = Policy(
            name="join_session",
            allow=Rules(
                JoinSession(
                    (User.traits["team"].contains("dev"))
                    & ((JoinSession.mode == "observer") | (JoinSession.mode == "peer"))
                    & (
                        (Session.owner.traits["team"].contains("dev"))
                        | (Session.owner.traits["team"].contains("intern"))
                    )
                ),
            ),
            deny=Rules(JoinSession(User.traits["team"].contains("intern"))),
        )

        ret = p.check(
            JoinSession(
                (User.traits["team"] == ("dev",))
                & (JoinSession.mode == "observer")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is True
        ), "a dev user can join a session from an intern user as an observer"

        ret = p.check(
            JoinSession(
                (User.traits["team"] == ("marketing",))
                & (JoinSession.mode == "observer")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is False
        ), "a marketing user cannot join a session from an intern user as an observer"

        ret = p.check(
            JoinSession(
                (User.traits["team"] == ("dev",))
                & (JoinSession.mode == "moderator")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is False
        ), "a dev user cannot join a session from an intern user as a moderator"

        ret = p.check(
            JoinSession(
                (User.traits["team"] == ("dev", "intern"))
                & (JoinSession.mode == "observer")
                & (Session.owner.traits["team"] == ("intern",))
            )
        )
        assert (
            ret.solves is False
        ), "a dev intern user cannot join a session from an intern user as an observer"

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
        ret = p.solve()
        assert ret.solves is True, "transformation has been applied"

    def test_policy_wrong_expr(self):
        """
        Test that policy mapping always returns the right value
        """
        with pytest.raises(ParameterError, match="should eval to string list"):
            PolicyMap(
                Select(
                    # Default is necessary to specify default empty sequence or type
                    Default(StringLiteral("test")),
                )
            )

        with pytest.raises(ParameterError):
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

        ret = Predicate(
            (s == ("ext-test", "ext-prod"))
            & (external["groups"] == ("admin-test", "admin-prod"))
        ).solve()
        assert ret.solves is True, "match and replace works"

        ret = Predicate(
            (s == ("dev-test", "dev-prod"))
            & (external["groups"] == ("dev-test", "dev-prod"))
        ).solve()
        assert ret.solves is True, "match and replace works default value"

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
        ret = p.solve()
        assert ret.solves is True, "match and replace works in login rules"

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

        ret = Predicate(
            (s == ("ext-test", "ext-prod"))
            & (external["groups"] == ("admin-test", "admin-prod"))
        ).solve()
        assert ret.solves is True, "match and replace works in policy maps"

        ret = Predicate(
            (s == ("dev-test", "dev-prod"))
            & (external["groups"] == ("dev-test", "dev-prod"))
        ).solve()
        assert (
            ret.solves is True
        ), "match and replace works in policy maps (default value)"

        # dev policy allows access to stage, and denies access to root
        dev = Policy(
            name="dev-stage",
            allow=Rules(
                AccessNode(
                    (AccessNode.login == "ubuntu") & (Node.labels["env"] == "stage")
                ),
            ),
            deny=Rules(
                AccessNode(
                    (AccessNode.login == "root") & (Node.labels["env"] == "prod")
                ),
            ),
        )

        # ext policy allows access to prod as ubuntu,
        # but requires strict recording mode
        ext = Policy(
            name="ext-stage",
            options=Options(
                recording_mode=RecordingMode.STRICT,
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
        ret = p.check(
            AccessNode((AccessNode.login == "root") & (Node.labels["env"] == "prod"))
        )
        assert ret.solves is False

        policy_names = try_login(
            s,
            (external["email"] == ("alice@wonderland.local",))
            & (external["groups"] == ("ext-stage",)),
        )
        assert policy_names == set(("ext-stage",))
        p = map_policies(policy_names, (dev, ext))

        # policy set will allow Alice to connect to prod if her
        # email is alice@wonderland.local
        ret = p.check(
            AccessNode(
                (AccessNode.login == "alice-wonderland.local")
                & (Node.labels["env"] == "prod")
            )
        )
        assert ret.solves is True

        # TODO: How to simplify testing and make it shorter?
        # TODO: How to connect policy mappings and
