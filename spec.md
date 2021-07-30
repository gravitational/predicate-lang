# Predicate

Predicate is a runtime, database and a mini-programming language
for access policies in distributed infrastructure.

Predicate interacts with databases, users and certificate authorities.
It is designed to be compatible with Teleport's RBAC. Teleport's users can
use both RBAC systems and Predicate in parallel and upgrade from one to another.

## Mini-language

Predicate comes with Prolog-inspired mini-language. It consists
of policies, users, facts and rules.

* User is a human or a non-interactive robot, e.g. bot or SSH server.

* Attributes are a key-value pairs describing properties of a user or a resource,
for example `env: prod`. A user can have none or several attributes.

* Facts state relationships between objects or define attributes, for example, `user(alice).` - a fact
that states that `alice` is a user. A fact `attribute(alice, env, prod).` states that alice has an attribute
`env: prod`.

* Rules define relationships between statements.

Admins can use rules to define group memberships.
This rule states that `U` is a member of a group `view` if `U` is a user and `U` is a member of a group `dev`:

```prolog
member(U, view) :-
  member(U, dev), user(U).
```

Rules like `allow` also govern access to resources. This rule
allows any user who is a member of group `dev` to access any server as `root`:

```prolog
allow(ssh, User, root, Server),
   member(User, dev).
```

Both facts and rules are clauses.

## Built-in clauses

* Groups assign users to a collection. For example `member(alice, dev).`
states that `alice` is a member of group `dev`.
* Allow and deny rules are evaluated by a target system to grant or deny access to the system.
These rules in more detail in "Allow and deny rules" section.
* Attribute-related  are used to assign attributes 

## Certificates and Attributes

Predicate encodes user's attributes in X.509 and SSH certificates.
The attributes in the certificates can not be modified or tampered with.
Any attribute requires a aser to get a new certificate, this in turn, leads
to usage of a more short lived certificates, ranging from hours, to minutes, or, in some cases,
seconds.

**Attributes**

Some attributes have a special meaning in certificates, and some are arbitrary.

For example, this attribute allows Alice to enable port forwarding in SSH:

```prolog
attribute(alice, allow_port_forwarding, true).
```

Because it's translated to SSH certificate extension `port_forwarding`.

Here is another attribute:

```prolog
attribute(alice, env, prod).
```

This is an arbitrary attribute that is simply encoded in X.509 and SSH certificate.

**Groups**

Group membership rules are **not** encoded in the certificates. 

```prolog
member(bob, prod).
```

It is important because a user may be assigned or unassigned a group to have their
access revoked.

**Roles**

Roles help Teleport's users to migrate from Teleport's RBAC to Predicate. For example,
here is a fact that assigns `alice` to role `admins`.

```prolog
role(alice, admins).
```

In this case, Alice's certificate will have Teleport role `admins` and Teleport's
RBAC will evaluate it as usual.

## User login and registration

Predicate's programs are applied on multiple stages of interactions of users.
Whenever an interactive user logs in via SSO, or SSH node registers with a join
token, predicate program can assign attributes based on OIDC Identity provider's
claims, SAML attribute statements and other third party infromation, for example AWS region
information presented by an SSH server during registration.

**Static assignments**

Facts can assign attributes or groups to users.

Any user logging in with email: `bob@example.com` will get an attribute `source: sso`
and is assigned to a group `sso`.

```prolog
attribute(bob@example.com, source, sso).
member(bob@example.com, admins).
```

These facts will be encoded in Bob's certificate.

**Dynamic assignments**

Predicate programmers can use rules to assign attributes based on external
information about users. The example below takes all traits from OIDC or SAML
and assigns them to attributes:

```prolog
attribute(U, Key, Val) :-
  sso_attribute(U, Key, Val).
```

Rules work with regular expression matches and group captures.

Here is an example assigns a user to a role `admin-test` if there is a matching
SAML attribute statement or OIDC claim `group: ssh_admin_test`:

```prolog
role(U, R) :-
    sso_attribute(U, group, Attr),
    regexp("ssh_admin_(?<group>.*)", Attr, Match),
    R = "admin-" + Match.group.
```

**Note:** See [roles SWI prolog implementation example](./role.pl) for a sample implementation.

## Access requests

Users can request access to resources, such as nodes, or request to be added
to additional groups.

Predicate supports this through access requests.

Users can submit approvals. Lisa and Forrest have approved the requests:

```prolog
approval(lisa, req).
approval(forrest, req).
```

A request is approved if there is enough approvals to match threshold:

```prolog
approved(Req) :-
    findall(User, approval(User, Req), List),
    length(List, Len),
    Len >= 2.
```

**Note:** See [roles SWI prolog implementation example](./aggregate.pl) for a sample implementation.

Once the request is approved, the following fact is added to the database,

```
% a fact added with TTL of 10 hours and distributed in the database of rules
member(alice, admins).
```

**Note** This model is better than Teleport's model that issues a new certificate, becasue
membership update

## Policies life-cycle

Zanzibar[0] paper describes a "New-enemy problem", when the system fails to respect ordering of policy updates:

Problem A: Neglecting ACL update order

1. Alice removes Bob from ACL of a folder;
2. Alice then asks Charlie to move new documents to the folder, where document
ACLs inherit from folder ACLs;
3. Bob should not be able to see the new documents, but may do so if the ACL check
neglects the ordering between the two ACL changes.

Problem B: Misapplying old ACL to new content

1. Alice removes Bob from ACL of the document.
2. Alice then asks Charlie to add new contents to the document.
3. Bob should not be able to see the new contents, but may do so, if the check
is if evaluated with a stale ACL list from before Bob's removal.

To solve these problems, Zanzibar providers two solutions:

* Spanner database to assign each ACL udpate a microsecond-accurate timestamp.
* Clients request "Zookie" 

**External consistency**

External consistency solves applying ACLs in the wrong order:

* Each ACL or content update gets the Tx as the timestamp value,
two casually related updates, x < y, will have Tx < Ty that reflects their casual ordering;
* A snapshot read of the database at timestamp T, will see casually ordered updates that match <= T
in a sorted order.

**Snapshot read with bounded staleness**

* The ACL check evaluation snapshot must not be staler than the casual timestamp
assigned to the content update. Given a content update at a timestamp Tc, a snapshot read
at timestamp >= Tc that all ACL updates that happen casually before the update
will be observed by the ACL check.

Predicate guarantees that:

* All clauses assigned to the same policy are replicated to the clients in a transaction.
* Other updates to the database performed in order will be replicated in order.
* Clients have a way to see if their cache is stale or missing some data in case of a partition.

TODO: replay the same scenarios as with Alice and Bob, this section is incomplete.

## Data model

* All facts and rules are stored in the database.
* Clauses have an optional expiration and policy attributes.
* Clients can retrieve, delete all clauses related to the same policy

```prolog
% show me all policies
policy(P).
P = admins;
P = devs.

% show me the spec for policy admins
listing(policy(mypolicy)).

?- listing(policy(mypolicy)).
policy(mypolicy) :-
    allow(ssh, alice, dev),
    deny(ssh, alice, admin).
```

**Note:** See [policies SWI prolog implementation example](./aggregate.pl) for a sample implementation.

* There is a classic GRPC API to add or remove policies and clauses in batch:
`DELETE rules WHERE policy = mypolicy`
`INSERT INTO rules(...)`

* And prolog interpreter frontend:

```prolog
delete(policy(mypolicy)).
insert(policy(mypolicy) :- ....)
listing(...)
```

This is where predicate diverges from classic prolog. In prolog, facts do not have expiration date,
can not be grouped by policy, and rules can not be retracted.

It becomes similar to [Datomic](https://www.datomic.com/), as Datomic is also a database of facts
with Datalog-like frontend.

**Scalability**

Clients can subscribe for updates for rules that they are interested in. For example, SSH node
can subscribe for allow and deny rules for SSH verb and group membership rules. This will allow
the system to scale.

## Implementation notes

TODO: Needs more work

Use [skyler prolog](https://github.com/mthom/scryer-prolog/blob/master/src/lib.rs) subset or build smaller version using [library](https://github.com/ekzhang/crepe)

For micro-interpreter. Load the interpreter state when database updates for internal systems, provide
a small interpreter shell to manipulate the database for fun and debugging (e.g. readonly).

## Policies, and Allow and Deny rules

TODO: work in progress

Allow rules and facts are in the form of:

```prolog
allow(Action, User, Target, Principal).
```

For example, this fact allow Alice to SSH into server `luna` as ssh principal `root`:

```prolog
allow(ssh, alice, luna, root).
```

Rules can be more complex and conditional. The rule below allows any member of
a group `admins` to SSH into any server that is a member of group `db` as root.

```prolog
allow(ssh, User, Host, root) :-
    member(User, admins),
    member(Host, db).
```

## Extensions

TODO: work in progress

Users can define custom predicates using web assembly and plug them into the built-in prolog interpreter

```prolog
wasm.time(Stamp) <- assigns time to Stamp
```

## Backwards compatibility

TODO: work in progress

Prolog frontend provides a nice way to interface with existing Teleport's objects:

```prolog
% lock alice out of the system for one hour
insert(
  lock(alice), 1h).
```

## Static analysis of access policies

TODO: Describe how one would use SMT solver like Z3 similar to Zelkova [1]

to find world-open, weak, or duplicate policies.

## References

* [0] [Zanzibar: Google’s Consistent, Global Authorization System](https://research.google/pubs/pub48190/).
* [1] [Zelkova: Semantic-based Automated Reasoning for AWS Access Policies using SMT](https://d1.awsstatic.com/Security/pdfs/Semantic_Based_Automated_Reasoning_for_AWS_Access_Policies_Using_SMT.pdf)
