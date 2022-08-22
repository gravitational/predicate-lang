## Predicate

Predicate is access control runtime and expression language.

Developers can write and test policies in python
using test driven development and advanced formal logic verification
to check if policies are weak, equivalent to insecure ones or fail certain conditions.

```python
# Define your policy using domain-specific language:
class User:
    '''
    User is a domain specific model (e.g. Teleport user)
    '''
    team = String("user.team")
    # name is username
    name = String("user.name")

# Write policy tests using advanced formal logic verification
class TestPolicy:
    def test_check_equiv(self):
        p = Predicate(
            User.team == "stage"
        )

        # This predicate is unsolvable, contradicts our main predicate
        ret, msg = p.check(Predicate(User.team != "stage"))
        assert ret == False
        assert "unsolvable" in msg

        # Two predicates are equivalent, if they return the same results,
        # equivalency is not equality, it's more broad.

        equiv, _ = p.equivalent(p)
        assert equiv == True, "predicate is equivalent to itself"

        equiv, _ = p.equivalent(Predicate((User.team == "stage") | (User.team == "stage")))
        assert equiv == True, "predicate is equivalent to it's redundant version"
```

### Out of the box support for common policies

Predicate supports most popular policies out of the box.
For example, users can query and test AWS policies in their account.

```python
class TestAWS:
    def test_aws_allow_policy(self, mixed_statement_policy):
        p = Predicate(aws.policy(mixed_statement_policy))

        ret, _ = p.check(Predicate(
            (aws.Action.resource == "arn:aws:s3:::example_bucket") & (aws.Action.action == "s3:ListBucket")))
        assert ret == True
```
