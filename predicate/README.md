# predicate

## Installing predicate

```bash
poetry install
```

Alternately, `poetry shell` can also be used to run `predicate`.

## Working with policies

### Example policy

```py
# access.py

from solver.ast import Duration
from solver.teleport import AccessNode, Node, Options, OptionsSet, Policy, Rules, User


class Teleport:
    p = Policy(
        name="access",
        loud=False,
        allow=Rules(
            AccessNode(
                ((AccessNode.login == User.name) & (User.name != "root"))
                | (User.traits["team"] == ("admins",))
            ),
        ),
        options=OptionsSet(Options((Options.max_session_ttl < Duration.new(hours=10)))),
        deny=Rules(
            AccessNode(
                (AccessNode.login == "mike")
                | (AccessNode.login == "jester")
                | (Node.labels["env"] == "prod")
            ),
        ),
    )

    def test_access(self):
        # Alice will be able to login to any machine as herself
        ret, _ = self.p.check(
            AccessNode(
                (AccessNode.login == "alice")
                & (User.name == "alice")
                & (Node.labels["env"] == "dev")
            )
        )
        assert ret is True, "Alice can login with her user to any node"

        # No one is permitted to login as mike
        ret, _ = self.p.query(AccessNode((AccessNode.login == "mike")))
        assert ret is False, "This role does not allow access as mike"

        # No one is permitted to login as jester
        ret, _ = self.p.query(AccessNode((AccessNode.login == "jester")))
        assert ret is False, "This role does not allow access as jester"
```

### Testing a policy

```bash
predicate test access.py
```

```bash
Running 1 tests:
  - test_access: ok
```

### Exporting a policy

```bash
predicate export access.py
```

```yaml
kind: policy
metadata:
  name: access
spec:
  allow:
    accessnode: (((access_node.login == user.name) && (!(user.name == "root"))) ||
      equals(user.traits["team"], ["admins"]))
  deny:
    accessnode: (((access_node.login == "mike") || (access_node.login == "jester"))
      || (node.labels["env"] == "prod"))
  options: (options.max_session_ttl < 36000000000000)
version: v1
```