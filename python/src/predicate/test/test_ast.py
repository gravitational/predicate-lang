import pytest
from predicate import ast, Predicate, String, ParameterError, regex, StringTuple, StringMap

# User-defined models here
class Server:
    '''
    Server is a domain-specific model (e.g. Teleport server)
    '''
    env = String("server.env")
    # login is SSH server login
    login = String("server.login")

class User:
    '''
    User is a domain specific model (e.g. Teleport user)
    '''
    team = String("user.team")
    # name is username
    name = String("user.name")

class TestAst:
    def test_check_equiv(self):
        """
        Demo how to test a simple condition, test one predicate
        against another and test whether two predicates are equivalent
        """
        p = Predicate(
            User.team == "stage"
        )

        # This predicate is unsolvable, contradicts our main prediccate
        ret, msg = p.check(Predicate(User.team != "stage"))
        assert ret == False
        assert "unsolvable" in msg

        # Two predicates are equivalent, if they return the same results,
        # equivalency is not equality, it's more broad.

        equiv, _ = p.equivalent(p)
        assert equiv == True, "predicate is equivalent to itself"

        equiv, _ = p.equivalent(Predicate((User.team == "stage") | (User.team == "stage")))
        assert equiv == True, "predicate is equivalent to it's redundant version"

    def test_two_symbols(self):
        """
        Test predicate that compares two symbols. Use simplify
        to simplify redundant expression
        """
        p = Predicate(Server.env == User.team)

        ret, _ = p.check(Predicate((Server.env == "prod") & (User.team == "prod")))
        assert ret == True, "this predicate holds when both values match"

        # user is not defined in the other predicate the check should fail
        # as we haven't defined all symbols
        with pytest.raises(ParameterError):
            p.check(Predicate(Server.env == "stage"))
        
        
        ## Try to simplify redundant obvious expression
        p = Predicate(
            (User.team == "stage") | (User.team == "stage")
        )
        assert str(p.simplify()) == "(string(user.team) == `stage`)"

        ## Simplify on non obvious expression is no-op
        p = Predicate(
            (User.team == "stage") | (Server.env == "stage")
        )
        assert str(p.simplify()) == "((string(user.team) == `stage`) | (string(server.env) == `stage`))"

    def test_queries(self):
        '''
        Let's build more complex expressions
        Any user can access servers marked with their team with their username
        '''
        p = Predicate((Server.env == User.team) & (Server.login == User.name))

        # Bob can access server with label prod with his name
        ret, _ = p.check(
            Predicate((Server.env == "prod") & (User.team == "prod") & (User.name == "bob") & (Server.login == "bob"))
        )
        assert ret == True

        # Query helps to ask more broad questions, e.g. can bob access servers labeled as "prod"?
        ret, _ = p.query(
            Predicate((Server.env == "prod") & (User.team == "prod") & (User.name == "bob")))
        assert ret == True, "Bob can access servers labeled as prod"

        # Can bob access servers labeled as stage?
        ret, _ = p.query(
            Predicate((Server.env == "stage") & (User.team == "prod") & (User.name == "bob")))
        assert ret == False, "Bob can't access servers labeled as stage"

        # Bob can't access server prod with someone else's name
        ret, _ = p.check(
            Predicate((Server.env == "prod") & (User.team == "prod") & (User.name == "bob") & (Server.login == "jim"))
        )
        assert ret == False, "Bob can't access prod with someone else's username"

        # Bob can't access server prod if Bob's team is not valid
        ret, _ = p.check(
            Predicate((Server.env == "prod") & (User.team == "stage") & (User.name == "bob") & (Server.login == "bob"))
        )
        assert ret == False, "Bob can't access servers of not his team"

    def test_invariants(self):
        '''
        Let's play with the concept of invariants. Invariant is a property that can't be
        violated. We can define invariant using calls to queries.
        '''

        ## No user except alice can get prod servers as root,
        ## For security invariant to hold, it has to be & with other rules
        prod = (Server.env == "prod") & (Server.login == "root")
        root = ((User.name == "alice") & prod)

        # "Deny condition if x" <==> condition & ~x
        general = ((User.team == Server.env) & (Server.login == User.name) & ~ prod)
        p = Predicate(
            root | general
        )

        # Alice can access prod as root
        ret, _ = p.check(
            Predicate((Server.env == "prod") & (User.name == "alice") & (Server.login == "root") & (User.team == "noop") )
        )
        assert ret == True, "Alice can access prod as root"

        # Bob can access stage as his name
        ret, _ = p.check(
            Predicate((Server.env == "stage") & (User.name == "bob") & (Server.login == "bob") & (User.team == "stage") )
        )
        assert ret == True, "Bob can access stage with his name"

        # Bob can't access prod as root
        ret, _ = p.check(
            Predicate((Server.env == "prod") & (User.name == "bob") & (Server.login == "root") & (User.team == "prod") )
        )
        assert ret == False, "Bob can't access prod as root"

        # Queries:
        ret, _ = p.query(
            Predicate((Server.env == "prod") & (Server.login == "root")))
        assert ret == True, "Is it possible for someone access prod as root"

        # Is it possible for bob to access prod as root?
        # this is invariant we can verify with call to query
        ret, _ = p.query(
            Predicate((Server.env == "prod") & (Server.login == "root") & (User.name == "bob")))
        assert ret == False, "Bob can't access prod as root"

        # This is a more broad, and more strict invariant:
        #
        # Is it possible for anyone who is not alice to access prod as root
        #
        # This could be a linter checker to make sure that whatever rules
        # people define, they can't access as root.
        #
        ret, _ = p.query(
            Predicate((Server.env == "prod") & (Server.login == "root") & (User.name != "alice")))
        assert ret == False, "Is it possible for anyone who is not alice to access prod as root?"

        # Let's try the case that contradicts the predicate
        violation = ((User.name == "jim") & (Server.env == "prod") & (Server.login == "root")  & ~prod)
        p = Predicate(
            root | violation
        )

        # Jim can access prod as root
        ret, _ = p.check(
            Predicate((Server.env == "prod") & (User.name == "jim") & (Server.login == "root") & (User.team == "noop") )
        )
        assert ret == False, "Jim can't access prod as root"

    def test_regex(self):
        p = Predicate(
            regex.parse("stage-.*").matches(User.team)
        )
        
        ret, _ = p.check(Predicate(User.team == "stage-test"))
        assert ret == True, "prefix patterns match"

        ret, _ = p.check(Predicate(User.team == "stage-other"))
        assert ret == True, "prefix patterns match"

        ret, _ = p.check(Predicate(User.team == "prod-test"))
        assert ret == False, "prefix pattern mismatch"


    def test_string_map(self):
        '''
        StringMaps are string key value pairs that support
        all string operations.
        '''
        m = StringMap('mymap')

        # maps could be part of the predicate
        p = Predicate(
            m["key"] == "val"
        )
        ret, _ = p.query(Predicate(m["key"] == "val"))
        assert ret == True

        ret, _ = p.query(Predicate(m["missing"] == "potato"))
        assert ret == False

        # multiple key-value checks
        m = StringMap('mymap', ["key", "key-2"])        
        p = Predicate(
            (m["key"] == "val") & (m["key-2"] == "val-2")
        )
        ret, _ = p.query(Predicate(m["key"] == "val"))
        assert ret == True


    def test_string_map_regex(self):
        '''
        StringMaps support regex matching as well
        '''
        # a bit clumsy, but very simple - declare keys in advance
        # to make sure undeclared keys can't be used
        m = StringMap('mymap', ["key"])

        # maps could be part of the predicate
        p = Predicate(
            regex.parse("env-.*").matches(m["key"])
        )
        ret, _ = p.query(Predicate(m["key"] == "env-prod"))
        assert ret == True


    def test_string_tuple(self):
        """
        Tests string tuples
        """
        t = StringTuple(["banana", "potato", "apple"])
        p = Predicate(
            t.contains("banana")
        )
        ret, _ = p.query(Predicate(t.contains("apple")))
        assert ret == True

    def test_regex_tuple(self):
        """
        Tests regexp tuples
        """
        t = regex.tuple(["banana-.*", "potato-.*", "apple-.*"])
        p = Predicate(
            t.matches("banana-smoothie")
        )
        ret, _ = p.query(Predicate(t.matches("apple-smoothie")))
        assert ret == True                

#
# TODO: sets, arrays?
# TODO: Transpile to teleport roles, IWS IAM roles
# 
