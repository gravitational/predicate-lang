import pytest

from .. import (
    Bool,
    Case,
    Default,
    Duration,
    If,
    Int,
    ParameterError,
    Predicate,
    Select,
    String,
    StringEnum,
    StringList,
    StringMap,
    StringSetMap,
    StringTuple,
    parse_regex,
    regex_tuple,
)


# User-defined models here
class Server:
    """
    Server is a domain-specific model (e.g. Teleport server)
    """

    env = String("server.env")
    # login is SSH server login
    login = String("server.login")


class User:
    """
    User is a domain specific model (e.g. Teleport user)
    """

    team = String("user.team")
    # name is username
    name = String("user.name")


class Request:
    """
    Request is a domain specific model, e.g. (Teleport approval thesholds)
    """

    approve = Int("request.approve")
    deny = Int("request.deny")


class Options:
    """
    Options is a class with mixed parameters
    """

    ttl = Duration("options.ttl")

    pin_source_ip = Bool("options.pin_source_ip")


class TestAst:
    def test_check_equiv(self):
        """
        Demo how to test a simple condition, test one predicate
        against another and test whether two predicates are equivalent
        """
        p = Predicate(User.team == "stage")

        # This predicate is unsolvable, contradicts our main prediccate
        ret, msg = p.check(Predicate(User.team != "stage"))
        assert ret is False
        assert "unsolvable" in msg

        # Two predicates are equivalent, if they return the same results,
        # equivalency is not equality, it's more broad.

        equiv, _ = p.equivalent(p)
        assert equiv is True, "predicate is equivalent to itself"

        equiv, _ = p.equivalent(
            Predicate((User.team == "stage") | (User.team == "stage"))
        )
        assert equiv is True, "predicate is equivalent to it's redundant version"

    def test_two_symbols(self):
        """
        Test predicate that compares two symbols. Use simplify
        to simplify redundant expression
        """
        p = Predicate(Server.env == User.team)

        ret, _ = p.check(Predicate((Server.env == "prod") & (User.team == "prod")))
        assert ret is True, "this predicate holds when both values match"

        # user is not defined in the other predicate the check should fail
        # as we haven't defined all symbols
        with pytest.raises(ParameterError):
            p.check(Predicate(Server.env == "stage"))

        # Try to simplify redundant obvious expression
        p = Predicate((User.team == "stage") | (User.team == "stage"))
        assert str(p.simplify()) == "(string(user.team) == `stage`)"

        # Simplify on non obvious expression is no-op
        p = Predicate((User.team == "stage") | (Server.env == "stage"))
        assert (
            str(p.simplify())
            == "((string(user.team) == `stage`) | (string(server.env) == `stage`))"
        )

    def test_queries(self):
        """
        Let's build more complex expressions
        Any user can access servers marked with their team with their username
        """
        p = Predicate((Server.env == User.team) & (Server.login == User.name))

        # Bob can access server with label prod with his name
        ret, _ = p.check(
            Predicate(
                (Server.env == "prod")
                & (User.team == "prod")
                & (User.name == "bob")
                & (Server.login == "bob")
            )
        )
        assert ret is True

        # Query helps to ask more broad questions, e.g. can bob access servers labeled as "prod"?
        ret, _ = p.query(
            Predicate(
                (Server.env == "prod") & (User.team == "prod") & (User.name == "bob")
            )
        )
        assert ret is True, "Bob can access servers labeled as prod"

        # Can bob access servers labeled as stage?
        ret, _ = p.query(
            Predicate(
                (Server.env == "stage") & (User.team == "prod") & (User.name == "bob")
            )
        )
        assert ret is False, "Bob can't access servers labeled as stage"

        # Bob can't access server prod with someone else's name
        ret, _ = p.check(
            Predicate(
                (Server.env == "prod")
                & (User.team == "prod")
                & (User.name == "bob")
                & (Server.login == "jim")
            )
        )
        assert ret is False, "Bob can't access prod with someone else's username"

        # Bob can't access server prod if Bob's team is not valid
        ret, _ = p.check(
            Predicate(
                (Server.env == "prod")
                & (User.team == "stage")
                & (User.name == "bob")
                & (Server.login == "bob")
            )
        )
        assert ret is False, "Bob can't access servers of not his team"

    def test_invariants(self):
        """
        Let's play with the concept of invariants. Invariant is a property that can't be
        violated. We can define invariant using calls to queries.
        """

        # No user except alice can get prod servers as root,
        # For security invariant to hold, it has to be & with other rules
        prod = (Server.env == "prod") & (Server.login == "root")
        root = (User.name == "alice") & prod

        # "Deny condition if x" <==> condition & ~x
        general = (User.team == Server.env) & (Server.login == User.name) & ~prod
        p = Predicate(root | general)

        # Alice can access prod as root
        ret, _ = p.check(
            Predicate(
                (Server.env == "prod")
                & (User.name == "alice")
                & (Server.login == "root")
                & (User.team == "noop")
            )
        )
        assert ret is True, "Alice can access prod as root"

        # Bob can access stage as his name
        ret, _ = p.check(
            Predicate(
                (Server.env == "stage")
                & (User.name == "bob")
                & (Server.login == "bob")
                & (User.team == "stage")
            )
        )
        assert ret is True, "Bob can access stage with his name"

        # Bob can't access prod as root
        ret, _ = p.check(
            Predicate(
                (Server.env == "prod")
                & (User.name == "bob")
                & (Server.login == "root")
                & (User.team == "prod")
            )
        )
        assert ret is False, "Bob can't access prod as root"

        # Queries:
        ret, _ = p.query(Predicate((Server.env == "prod") & (Server.login == "root")))
        assert ret is True, "Is it possible for someone access prod as root"

        # Is it possible for bob to access prod as root?
        # this is invariant we can verify with call to query
        ret, _ = p.query(
            Predicate(
                (Server.env == "prod") & (Server.login == "root") & (User.name == "bob")
            )
        )
        assert ret is False, "Bob can't access prod as root"

        # This is a more broad, and more strict invariant:
        #
        # Is it possible for anyone who is not alice to access prod as root
        #
        # This could be a linter checker to make sure that whatever rules
        # people define, they can't access as root.
        #
        ret, _ = p.query(
            Predicate(
                (Server.env == "prod")
                & (Server.login == "root")
                & (User.name != "alice")
            )
        )
        assert (
            ret is False
        ), "Is it possible for anyone who is not alice to access prod as root?"

        # Let's try the case that contradicts the predicate
        violation = (
            (User.name == "jim")
            & (Server.env == "prod")
            & (Server.login == "root")
            & ~prod
        )
        p = Predicate(root | violation)

        # Jim can access prod as root
        ret, _ = p.check(
            Predicate(
                (Server.env == "prod")
                & (User.name == "jim")
                & (Server.login == "root")
                & (User.team == "noop")
            )
        )
        assert ret is False, "Jim can't access prod as root"

    def test_regex(self):
        p = Predicate(parse_regex("stage-.*").matches(User.team))

        ret, _ = p.check(Predicate(User.team == "stage-test"))
        assert ret is True, "prefix patterns match"

        ret, _ = p.check(Predicate(User.team == "stage-other"))
        assert ret is True, "prefix patterns match"

        ret, _ = p.check(Predicate(User.team == "prod-test"))
        assert ret is False, "prefix pattern mismatch"

    def test_concat(self):
        p = Predicate(Server.login == User.name + "-login")
        ret, _ = p.check(
            Predicate((Server.login == "alice-login") & (User.name == "alice"))
        )
        assert ret is True, "pattern matches suffix"

        p = Predicate(Server.login == "login-" + User.name)
        ret, _ = p.check(
            Predicate((Server.login == "login-alice") & (User.name == "alice"))
        )
        assert ret is True, "pattern matches prefix"

        p = Predicate(Server.login == "login-" + User.name + "-user")
        ret, _ = p.check(
            Predicate((Server.login == "login-alice-user") & (User.name == "alice"))
        )
        assert ret is True, "pattern matches suffix and prefix"

        # TODOs:
        # https://github.com/Z3Prover/z3/blob/9f9543ef698adc77252ed366e6d85cc71e4b8c89/src/ast/rewriter/seq_axioms.cpp#L1044
        # not implemented yet

    def test_delimiter(self):
        """
        Test splitting at delimiter.
        """
        p = Predicate(Server.login == User.name.before_delimiter("@"))
        ret, _ = p.check(
            Predicate((Server.login == "alice") & (User.name == "alice@example.com"))
        )
        assert ret is True, "splitting before delimiter works"

        ret, _ = p.check(
            Predicate((Server.login == "") & (User.name == "alice-example.com"))
        )
        assert ret is True, "delimiter not present, string renders to empty"

        p = Predicate(Server.login == User.name.after_delimiter("@"))
        ret, _ = p.check(
            Predicate(
                (Server.login == "example.com") & (User.name == "alice@example.com")
            )
        )
        assert ret is True, "splitting after delimiter works"

        ret, _ = p.check(
            Predicate((Server.login == "") & (User.name == "alice-example.com"))
        )
        assert ret is True, "delimiter not present, string renders to empty"

    def test_replace(self):
        """
        Test replace string characters.
        """
        p = Predicate(Server.login == User.name.replace("@", "-"))
        ret, z = p.check(
            Predicate(
                (Server.login == "alice-example.com")
                & (User.name == "alice@example.com")
            )
        )
        assert ret is True, "replacing works"

        ret, _ = p.check(
            Predicate(
                (Server.login == "alice+example.com")
                & (User.name == "alice+example.com")
            )
        )
        assert ret is True, "character not present, no effect"

    def test_upper_lower(self):
        """
        Test upper lower case.
        """
        p = Predicate(Server.login == User.name.upper())
        ret, z = p.check(Predicate((Server.login == "ALICE") & (User.name == "AlicE")))
        assert ret is True, "uppercase works"

        p = Predicate(Server.login == User.name.lower())
        ret, z = p.check(Predicate((Server.login == "alice") & (User.name == "AlicE")))
        assert ret is True, "lowercase works"

    def test_string_list_init(self):
        # filter example - we only keep fruits by copying them over
        fruits = StringList("fruits", ("apple", "strawberry", "banana"))

        p = Predicate((fruits == ("apple", "strawberry", "banana")))
        ret, _ = p.solve()
        assert ret is True, "values match"

    def test_string_list_with_if(self):
        basket = StringList("basket")
        # filter example - we only keep fruits by copying them over
        fruits = StringList(
            "fruits",
            If(
                basket.contains("banana"),
                basket.add_if_not_exists("blueberry"),
                basket,
            ),
        )

        p = Predicate(
            (basket == ("strawberry", "apple", "banana"))
            & (fruits == ("blueberry", "strawberry", "apple", "banana"))
        )
        ret, _ = p.solve()
        assert ret is True, "blueberry was added"

        p = Predicate(
            (basket == ("apple", "strawberry")) & (fruits == ("apple", "strawberry"))
        )
        p.solve()
        assert ret is True, "blueberry was not added"

    def test_string_list_transform_value(self):
        external = StringList("external")
        # transform example - we reference another variable and transform
        traits = StringList("traits", external.replace("@", "-"))

        p = Predicate(
            (external == ("alice@wonderland.local",))
            & (traits == ("alice-wonderland.local",))
        )
        ret, _ = p.solve()
        assert ret is True, "transformation has been applied"

        p = Predicate((external == ()) & (traits == ()))
        ret, _ = p.solve()
        assert ret is True, "transformation on empty list is empty"

    def test_string_set_map_contains(self):
        traits = StringSetMap("mymap")
        p = Predicate(traits["key"].contains("potato"))
        ret, _ = p.check(
            Predicate(
                (traits["key"] == ("apple", "potato", "banana"))
                | (traits["key"] == ("strawberry",))
            )
        )
        assert ret is True, "values match"

        ret, _ = p.check(Predicate(traits["key"] == ("apple", "banana")))
        assert ret is False, "values don't match"

    def test_string_set_map_contains_regex(self):
        traits = StringSetMap(
            "mymap",
            {
                "groups": ("fruit-apple", "veggie-potato", "fruit-banana"),
            },
        )
        p = Predicate(traits["groups"].contains_regex("fruit-.*"))
        ret, _ = p.solve()
        assert ret is True, "values match regular expression"

        traits = StringSetMap(
            "mymap",
            {
                "groups": ("apple", "potato", "banana"),
            },
        )
        with pytest.raises(ParameterError) as exc:
            p = Predicate(traits["groups"].contains_regex("fruit-apple"))
            ret, _ = p.solve()
        assert "unsolvable" in str(exc.value)

    def test_string_set_map_len(self):
        traits = StringSetMap(
            "mymap",
            {
                "groups": ("fruit-apple", "veggie-potato", "fruit-banana"),
            },
        )
        p = Predicate(traits["groups"].len() == 3)
        ret, _ = p.solve()
        assert ret is True, "counts properly"

        p = Predicate(traits["missing"].len() == 0)
        ret, _ = p.solve()
        assert ret is True, "missing key results in empty count"

        with pytest.raises(ParameterError):
            p = Predicate(traits["missing"].len() == 1)
            ret, _ = p.solve()

    def test_string_set_map_len_undefined(self):
        approvals = StringSetMap("mymap")
        p = Predicate(approvals["my-policy"].len() > 2)
        ret, _ = p.solve()
        assert ret is True, "predicate solves"

        ret, _ = p.check(Predicate(approvals["my-policy"].len() == 3))
        assert ret is True, "predicate solves"

        ret, _ = p.check(Predicate(approvals["my-policy"].len() == 2))
        assert ret is False, "predicate fails to solve"

        ret, _ = p.query(Predicate(approvals["my-policy"].len() == 2))
        assert ret is False, "predicate fails to solve with query as well"

    def test_string_set_map_first(self):
        traits = StringSetMap(
            "mymap",
            {
                "groups": ("fruit-apple", "veggie-potato", "fruit-banana"),
            },
        )
        p = Predicate(traits["groups"].first() == "fruit-apple")
        ret, _ = p.solve()
        assert ret is True, "gets first value"

        traits = StringSetMap(
            "mymap",
            {
                "groups": ("", "potato", "banana"),
            },
        )

        p = Predicate(traits["groups"].first() == "potato")
        ret, _ = p.solve()
        assert ret is True, "gets first non-empty value"

        traits = StringSetMap(
            "mymap",
            {
                "groups": (),
            },
        )

        p = Predicate(traits["groups"].first() == "")
        ret, _ = p.solve()
        assert ret is True, "returns empty string if no value"

    def test_string_set_map_add_value(self):
        traits = StringSetMap("mymap")
        p = Predicate(
            # this predicate is always true, we always add strawberry
            traits.add_value("fruits", "strawberry")["fruits"].contains("strawberry")
        )
        ret, _ = p.check(
            Predicate(traits["fruits"] == ("strawberry", "apple", "banana"))
        )
        assert ret is True, "values match with strawberry"

        ret, _ = p.check(Predicate(traits["fruits"] == ("apple", "banana")))
        assert ret is True, "values match even if strawberry is missing"

    def test_string_set_map_with_values(self):
        external = StringSetMap("external")
        # filter example - we only keep fruits by copying them over
        traits = StringSetMap(
            "traits",
            {
                "our-fruits": external["fruits"],
            },
        )
        p = Predicate(
            (external["fruits"] == ("strawberry", "apple", "banana"))
            & (traits["our-fruits"].contains("strawberry"))
        )
        ret, _ = p.solve()
        assert ret is True, "values match with strawberry"

        with pytest.raises(ParameterError) as exc:
            # this predicate is unsolvable
            p = Predicate(
                (external["fruits"] == ("apple", "banana"))
                & (traits["our-fruits"].contains("strawberry"))
            )
            p.solve()
        assert "unsolvable" in str(exc.value)

    def test_string_set_map_list_init(self):
        # filter example - we only keep fruits by copying them over
        traits = StringSetMap(
            "traits",
            {
                "fruits": ("apple", "strawberry", "banana"),
                "veggies": ("potato",),
            },
        )
        p = Predicate(
            (traits["fruits"] == ("apple", "strawberry", "banana"))
            & (traits["veggies"] == ("potato",))
        )
        ret, _ = p.solve()
        assert ret is True, "values match with strawberry"

    def test_string_set_map_remove_keys(self):
        # filter example - we only keep fruits by copying them over
        traits = StringSetMap(
            "traits",
            {
                "fruits": ("apple", "strawberry", "banana"),
                "veggies": ("potato",),
            },
        ).remove_keys("veggies")
        p = Predicate(
            (traits["fruits"] == ("apple", "strawberry", "banana"))
            & (traits["veggies"] == ())
        )
        ret, _ = p.solve()
        assert ret is True, "veggies is empty"

    def test_string_set_map_overwrite(self):
        traits = StringSetMap(
            "traits",
            {
                "fruits": ("apple", "strawberry", "banana"),
            },
        ).overwrite({"veggies": ("potato",)})
        p = Predicate(
            (traits["fruits"] == ("apple", "strawberry", "banana"))
            & (traits["veggies"] == ("potato",))
        )
        ret, _ = p.solve()
        assert ret is True, "overwritten with added potato values"

    def test_string_set_map_with_if(self):
        external = StringSetMap("external")
        # filter example - we only keep fruits by copying them over
        traits = StringSetMap(
            "traits",
            {
                "our-fruits": If(
                    external["fruits"].contains("banana"),
                    external["fruits"].add_if_not_exists("blueberry"),
                    external["fruits"],
                )
            },
        )
        p = Predicate(
            (external["fruits"] == ("strawberry", "apple", "banana"))
            & (traits["our-fruits"] == ("blueberry", "strawberry", "apple", "banana"))
        )
        ret, _ = p.solve()
        assert ret is True, "blueberry was added"

        p = Predicate(
            (external["fruits"] == ("apple", "strawberry"))
            & (traits["our-fruits"] == ("apple", "strawberry"))
        )
        p.solve()
        assert ret is True, "blueberry was not added"

    def test_string_set_map_transform_value(self):
        external = StringSetMap("external")
        # transform example - we reference another variable and transform
        traits = StringSetMap(
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

        p = Predicate((external["email"] == ()) & (traits["login"] == ()))
        ret, _ = p.solve()
        assert ret is True, "transformation on empty list is empty"

    def test_string_map(self):
        """
        StringMaps are string key value pairs that support
        all string operations.
        """
        m = StringMap("mymap")

        # maps could be part of the predicate
        p = Predicate(m["key"] == "val")
        ret, _ = p.query(Predicate(m["key"] == "val"))
        assert ret is True, "values match"

        ret, _ = p.query(Predicate(m["key"] != "val"))
        assert ret is False, "values don't match"

        # check raises parameter error because key 'key' is missing
        with pytest.raises(ParameterError):
            ret, _ = p.check(Predicate(m["missing"] == "potato"))

        ret, _ = p.query(Predicate(m["missing"] == "potato"))
        assert (
            ret is False
        ), "query that does not have matching keys should fail, otherwise you would get query match both predicates with keys missing and exact matches"

        ret, _ = p.solves_with(Predicate(m["missing"] == "potato"))
        assert (
            ret is True
        ), "contrary to query statement above, this predicate does not contradict the statement m['key'] == 'val', both can be true at the same time"

        # multiple key-value checks
        m = StringMap("mymap")
        p = Predicate((m["key"] == "val") & (m["key-2"] == "val-2"))

        ret, _ = p.query(Predicate(m["key"] == "val"))
        assert ret is True, "query on subset of keys is successfull"

        # check will raise error when there is ambiguity because
        # not all keys have been specified
        with pytest.raises(ParameterError):
            ret, _ = p.check(Predicate(m["key"] == "val"))

        ret, _ = p.check(Predicate((m["key"] == "val") & (m["key-2"] == "val-2")))
        assert ret is True, "check, all keys and values, match"

        ret, _ = p.check(
            Predicate(
                (m["key"] == "val") & (m["key-2"] == "val-2") & (m["key-3"] == "val")
            )
        )
        assert ret is True, "check is OK when the right side has superset of keys"

        ret, _ = p.check(Predicate((m["key"] == "val") & (m["key-2"] == "wrong")))
        assert ret is False, "check fails when some values don't match"

        ret, _ = p.check(
            Predicate(
                (m["key"] == "val") & (m["key-2"] == "wrong") & (m["key-3"] == "val")
            )
        )
        assert (
            ret is False
        ), "check fails when the right side has superset of keys, but values don't match"

    def test_string_enum(self):
        """
        StringEnum are predefined values
        """
        e = StringEnum("fruits", set(["banana", "apple", "strawberry"]))

        # enums could be part of the predicate
        p = Predicate(
            e.one_of()  # equivalent of  (e == 'apple') | (e == 'banana') | (e == 'strawberry')
        )
        ret, _ = p.query(Predicate(e == "banana"))
        assert ret is True, "values match"

        ret, _ = p.query(Predicate(e == "potato"))
        assert ret is False, "values don't match"

        ret, _ = p.query(Predicate(e == ""))
        assert ret is False, "values don't match"

        # this predicate is unsolvable, so all tests against it will raise error
        p = Predicate(e == "potato")
        with pytest.raises(ParameterError):
            ret, _ = p.query(Predicate(e == "banana"))
            assert ret is True, "values match"

    def test_string_enum_comparison(self):
        """
        StringEnum are predefined values
        """
        # fruits by size
        e = StringEnum("fruits", [(0, "strawberry"), (1, "apple"), (2, "watermelon")])

        # enums could be part of the predicate and can provide constraints
        p = Predicate((e > "apple") | (e == "apple"))
        ret, _ = p.query(Predicate(e == "apple"))
        assert ret is True, "values match"

        ret, _ = p.query(Predicate(e == "watermelon"))
        assert ret is True, "passes equation"

        ret, _ = p.query(Predicate(e == "strawberry"))
        assert ret is False, "values don't match the equation"

        ret, _ = p.query(Predicate(e == "strawberr"))
        assert ret is False, "unsupported value fails"

    def test_string_map_regex(self):
        """
        StringMaps support regex matching as well
        """
        # a bit clumsy, but very simple - declare keys in advance
        # to make sure undeclared keys can't be used
        m = StringMap("mymap")

        # maps could be part of the predicate
        p = Predicate(parse_regex("env-.*").matches(m["key"]))
        ret, _ = p.query(Predicate(m["key"] == "env-prod"))
        assert ret is True

    def test_string_tuple(self):
        """
        Tests string tuples
        """
        t = StringTuple(["banana", "potato", "apple"])
        p = Predicate(t.contains("banana"))
        ret, _ = p.query(Predicate(t.contains("apple")))
        assert ret is True

    def test_regex_tuple(self):
        """
        Tests regexp tuples
        """
        t = regex_tuple(["banana-.*", "potato-.*", "apple-.*"])
        p = Predicate(t.matches("banana-smoothie"))
        ret, _ = p.query(Predicate(t.matches("apple-smoothie")))
        assert ret is True

    def test_int(self):
        """
        Test int tests integer operations
        """
        p = Predicate(Request.approve == 1)

        ret, _ = p.check(Predicate(Request.approve == 1))
        assert ret is True, "solves with simple equality check"

        p = Predicate((Request.approve > 1) & (Request.approve < 3))

        ret, _ = p.check(Predicate(Request.approve == 2))
        assert ret is True, "solves with simple boundary check"

        ret, _ = p.check(Predicate(Request.approve == 5))
        assert ret is False, "solves with simple boundary check"

    def test_duration(self):
        """
        Test int tests integer operations
        """
        p = Predicate(
            Options.ttl == Duration.new(hours=5),
        )

        ret, _ = p.check(Predicate(Options.ttl == Duration.new(hours=5)))
        assert ret is True, "solves with simple equality check"

        p = Predicate(
            (Options.ttl > Duration.new(seconds=10))
            & (Options.ttl < Duration.new(hours=5))
        )

        ret, _ = p.check(Predicate(Options.ttl == Duration.new(hours=3)))
        assert ret is True, "solves with simple boundary check"

        ret, _ = p.check(Predicate(Options.ttl == Duration.new(hours=6)))
        assert ret is False, "solves with simple boundary check"

    def test_bool(self):
        """
        Test int tests integer operations
        """
        p = Predicate(
            Options.pin_source_ip == True,
        )

        ret, _ = p.check(Predicate(Options.pin_source_ip == True))
        assert ret is True, "solves with simple equality check"

        ret, _ = p.check(Predicate(Options.pin_source_ip == False))
        assert ret is False, "solves with simple boundary check"

    def test_select(self):
        external = StringSetMap("external")

        s = Select(
            Case(external["groups"].contains("admin"), ("admin",)),
            # Default is necessary to specify default empty sequence or type
            Default(())
            # {Claim: "role", Value: "^admin-(.*)$", Roles: []string{"role-$1", "bob"}},
            # Case(external['groups'].matches_regexp('test-.*'), (external['groups'].replace('admin-', 'role-').add('bob')))
        )

        ret, _ = Predicate(
            (s == ("admin",)) & (external["groups"] == ("admin", "other"))
        ).solve()
        assert ret is True, "simple match works"

        ret, _ = Predicate(
            (s == ()) & (external["groups"] == ("nomatch", "other"))
        ).solve()
        assert ret is True, "no match results in default"

        # once you have a select defined, you can specify set of roles and policies

    def test_select_regex(self):
        external = StringSetMap("external")

        s = Select(
            Case(external["groups"].contains_regex("admin-.*"), ("admin",)),
            # Default is necessary to specify default empty sequence or type
            Default(()),
        )

        ret, _ = Predicate(
            (s == ("admin",)) & (external["groups"] == ("admin-test", "other"))
        ).solve()
        assert ret is True, "simple match works"

        ret, _ = Predicate(
            (s == ()) & (external["groups"] == ("nomatch", "other"))
        ).solve()
        assert ret is True, "no match results in default"

    def test_select_regex_replace(self):
        external = StringSetMap("external")

        s = Select(
            Case(
                external["groups"].contains_regex("admin-.*"),
                external["groups"].replace("admin-", "ext-"),
            ),
            # Default is necessary to specify default empty sequence or type
            Default(external["groups"]),
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
