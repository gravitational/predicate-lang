# Predicate

Predicate is a runtime, and a domain-specific language
for defining access policies in distributed infrastructure.

Predicate's rules are compiled to a WASM program,
and are used to issue short lived certificates and verify access to resources.

Before compilation, the rules are verified by Z3 to prove or disprove
Predicate's logical statements and constraints. Predicate gives strong guarantees
about statements verified using theorem prover. The generated program
provides interface to query and introspect it's statements.

**Migration Note**
Predicate is designed to complement Teleport's existing RBAC system.
Teleport's users can use both existing RBAC system and Predicate in parallel.

## Domain-specific language

Predicate consists of policies, users, facts and rules.

Predicate is a library with DSL for most common programming languages.
It will compile to a WASM program that can be evaluated by any runtime that supports WASM.

In this spec, we will be using Prolog to specify predicate expressions,
In the real world, we will use domain-specific languages.

### Terminology

* User is a human or a non-interactive robot, e.g. bot or SSH server.

* Attributes are a key-value pairs describing properties of a user or a resource,
for example `env: prod`. A user can have none or several attributes.

* Facts state relationships between objects or define attributes, for example, `user(alice);` is a fact
that states that `alice` is a user. A fact `attribute(alice, env, prod);` states that alice has an attribute
`env: prod`.

* Rules define relationships between statements.

Admins can use rules to define group memberships.
This rule states that `U` is a member of a group `view` if `U` is a user and `U` is a member of a group `dev`:

```prolog
member(U, view) <-
  member(U, dev), user(U);
```

Rules like `allow` also govern access to resources. This rule
allows any user who is a member of group `dev` to access any server as `root`:

```prolog
allow(ssh, User, root, Server) <-
   member(User, dev);
```

Both facts and rules are clauses.

## Built-in clauses

* Groups assign users to a collection. For example `member(alice, dev);`
states that `alice` is a member of group `dev`.

* Allow and deny rules are evaluated by a target system to grant or deny access to the system.
These rules in more detail in "Allow and deny rules" section. For example,

`allow(ssh, alice, luna, root);` allows user `alice` to ssh into server `luna` as SSH principal `root`.

* Attribute clauses are used to assign attributes to certificates when users log in.
For example, `attribute(alice, source, sso);` assigns user Alice attribute `sso` that is encoded in the certificate.

* Users can request access to multiple parts of the infrastructure and other users can approve or deny those requests.
Approvals and access requests are facts. For example, if Alice requests to be added to a group, request is logged as: `request(member, alice, dev, 1h).`
Approvals show approvals of a request `approve(alice, req1);`.

## Certificates and Attributes

Predicate encodes user's attributes in X.509 and SSH certificates.
The attributes in the certificates can not be modified or tampered with.
Any attribute requires a user to get a new certificate, this in turn, leads
to usage of a more short lived certificates, ranging from hours, to minutes, or, in some cases,
seconds.

**Attributes**

Some attributes have a special meaning in certificates, and some are arbitrary.

For example, this attribute allows Alice to enable port forwarding in SSH:

```prolog
attribute(alice, port_forwarding, true);
```

The attribute above translated to SSH certificate extension `port_forwarding`.

Here is another attribute:

```prolog
attribute(alice, env, prod);
```

This is an arbitrary attribute that is simply encoded in X.509 and SSH certificate.

**Roles**

Roles help Teleport's users to migrate from Teleport's RBAC to Predicate. For example,
here is a fact that assigns `alice` to role `admins`.

```prolog
role(alice, admins);
```

In this case, Alice's certificate will have Teleport role `admins` and Teleport's
RBAC will evaluate it as usual.

## Groups

Group membership rules are **not** encoded in the certificates.

```prolog
member(bob, prod);
```

It is important because a user may be assigned or unassigned a group to have their
access revoked. Clients fetch group membership, and allow and deny clauses and use them to evaluate
access each time a user performs an action.

## User login and registration

Predicate's programs are applied on multiple stages of user interaction with a program.

Whenever an interactive user logs in via SSO, or SSH node registers with a join
token, predicate program can assign attributes based on OIDC Identity provider's
claims, SAML attribute statements and other third party information, for example AWS region
information presented by an SSH server during registration.

**Static assignments**

Facts can assign attributes or groups to users.

Any user logging in with email: `bob@example.com` will get an attribute `source: sso`
and is assigned to a group `sso`.

```prolog
attribute(bob@example.com, source, sso);
member(bob@example.com, admins);
```

Attribute `source: sso` will be encoded in Bob's certificate, but `member` will not.

**Dynamic assignments**

Predicate programmers can use rules to assign attributes based on external
information about users. The example below takes all traits from OIDC or SAML
and assigns them to attributes:

```prolog
attribute(U, Key, Val) <-
  sso_attribute(U, Key, Val);
```

Rules work with regular expression matches and group captures.

Here is an example assigns a user to a role `admin-test` if there is a matching
SAML attribute statement or OIDC claim `group: ssh_admin_test`:

```prolog
role(U, R) <-
    sso_attribute(U, group, Attr),
    regexp("ssh_admin_(?<group>.*)", Attr, Match),
    (R = "admin-" + Match.group);
```

**Note:** See [roles SWI prolog implementation example](./prolog/role.pl) for a sample implementation.

## External facts and collections

Often, administrators of real-world systems need to consult external systems
to evaluate access control. For example, information about whether a user
is administrator of a system can come from external HR system. This creates a problem,
if a system is down, non-operational or changed, the integration with this system
has to be changed and all access rules have to be rewritten. It also could be hard
to verify statements and integration logic with any system.

Predicate helps to solves this problem by providing integration points
with external rules databases. For example, HR system can be presented
as a rules database with rules:

```prolog
hr_attribute(alice, group, admins).
hr_attribute(ivan, group, users).
```

The integration logic will sync the rules database and make them
accessible to the WASM program of predicate.

Developers can write tests replacing the real database with test data.

A Predicate program can access this list like any other database of rules:

```prolog
member(U, dev) <-
  contains(U, hr_attribute);
```

## Policies, and Allow and Deny rules

TODO: work in progress.

Allow rules and facts are in the form of:

```prolog
allow(Action, User, Target, Principal);
```

Rules clauses can be more complex and conditional. The rule below allows any member of
a group `admins` to SSH into any server that is a member of group `db` as root.

```prolog
allow(ssh, User, Host, root) <-
    member(User, admins),
    member(Host, db);
```

Allow and deny rules can refer to Users' attributes encoded in the certificates,
can address group memberships, and can address target attributes and node labels.

In the example below, users can login into host as any principal that is encoded
in their certificate as attribute `login` to any host that matches the label `host_label`
also encoded in the certificate:

```prolog
allow(ssh, User, Host, Principal) <-
    attribute(User, host_label, L),
    label(Host, host_label, L),
    attribute(User, login, X),
    (Principal = X);
```

Allow and deny rules sometimes need to be grouped together:

```prolog
% Alice can login into any host as root,
allow(ssh, alice, root, H) <-
  (H = _);
% Except the hosts that are labeled production
deny(ssh, alice, root, H) <-
  label(H, env, prod);
```

These two rules should always be fetched and evaluated together. If predicate
only sees the allow, that would let Alice to access any host.

Policy is a named group of clauses that guarantees that rules will be fetched
by predicate clients in a transaction:

```prolog
policy(admins) <-
  member(alice, devs);
  % Alice can login into any host as root,
  allow(ssh, alice, root, H) <-
    (H = _);
  % Except the hosts that are labeled production
  deny(ssh, alice, root, H) <-
    label(H, env, prod);
```

## Access requests

Users can request access to resources, such as nodes, or request to be added
to additional groups.

Predicate supports this through access requests.

Alice requests to be added to group `admins` for `1h`:

`request(member, alice, dev, 1h);`

Alice requests SSH access to a node `luna` for `10m` as `root`:

`request(ssh, alice, root, luna, 10m);`

Alice requests an extra attribute for `10m`:

`request(attribute, alice, env, prod, 10m);`

Users can submit their approves and denies as facts to the predicate database.

Lisa and Forrest have approved the requests:

```prolog
approve(lisa, req1, "please proceed with caution");
approve(forrest, req1, "no comment");
deny(sasha, req1, "you shall not pass");
```

A request is approved if there is enough approvals to match the threshold:

```prolog
approved(Req) <-
    findall(User, approve(User, Req), List),
    length(List, Len),
    Len >= 2;
```

**Note:** See [roles SWI prolog implementation example](./prolog/aggregate.pl) for a sample implementation.

Once the request is approved, the following fact is added to the database,

```
% a fact added with TTL of 10 hours and distributed in the database of rules
member(alice, admins);
```

**Members vs Attributes**

Adding member fact to the database is different than Teleport's model that issues a new certificate, because
membership update and expiration is propagated instantaneously, and can be revoked
if the member fact is deleted from the database:

`member(alice, admins);`

The disadvantage compared to existing Teleport's model is that Teleport's access requests
are embedded in the certificate and can be reviewed by other organizations.

Requesting attribute is similar to Teleport's model, because once `attribute` is added to the database,
a user can issue a new certificate:

`attribute(alice, env, prod);`

If you combine this with a rule on the leaf or cluster, users will be added to new groups:

```prolog
member(U, admins) <-
  attribute(U, env, prod);
```


## Appendix A: Data Model - Variant 1

* All predicate clauses are stored in the database.
* Each clause has a unique auto generated id. Users can delete or update the clause by id.
* Every clauses have origin attribute, denoting a user that created and updated it.
* Clauses have an optional expiration and policy attributes. When clause expires,
clients reload the state of the prolog interpreter.
* Clients can retrieve, delete all clauses related to the same policy just like with any other
database.

```prolog
% show me all policies
policy(P).
P = admins;
P = devs.

% show me the spec for policy admins
listing(policy(mypolicy));

?- listing(policy(mypolicy)).
policy(mypolicy) <-
    allow(ssh, alice, dev),
    deny(ssh, alice, admin);
```

**Note:** See [policies SWI prolog implementation example](./prolog/aggregate.pl) for a sample implementation.

* There is a classic GRPC API to add or remove policies and clauses in batch:
`DELETE rules WHERE policy = mypolicy`
`INSERT INTO rules(...)`

* And prolog interpreter frontend:

```prolog
% delete clause by spec or ID
delete(policy(mypolicy));
% create a new clause
create(policy(mypolicy) :- ....);
% list clauses matching pattern
listing(...);
% update clause by ID
update();
```

This is where predicate diverges from classic prolog. In prolog, facts do not have expiration date,
can not be grouped by policy, and rules can not be retracted.

It becomes similar to [Datomic](https://www.datomic.com/), as Datomic is also a database of facts
with Datalog-like frontend.

**Scalability**

This fact allow Alice to SSH into server `luna` as ssh principal `root`:

```prolog
allow(ssh, alice, luna, root);
```

Internally, these allow rules are stored in a tree:

```
allow
|
+----ssh 
      |
      +---alice (id=1, created=bob@example.com, policy=mypolicy, ttl=1h)
```

This allows clients to subscribe to relevant parts of the rules, e.g. SSH nodes
can only watch SSH rules updates.

Clients can subscribe for updates for rules that they are interested in. For example, SSH node
can subscribe for allow and deny rules for SSH verb and group membership rules. This will allow
the system to scale.

Each node has to fetch all membership rules, locks, so there should be a limit on maximum number
of those in the system.

### Policies life-cycle for Variant 1

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

* Spanner database to assign each ACL update a microsecond-accurate timestamp.
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

## Appendix B. Forrest Critique Of Variant 1 Data Model

I see a lot of merit in the flexibility and simplicity of this system,
but I'm concerned about the usability of the actual syntax/workflow.
It is different enough from how most programming and configuration languages work,
but similar enough in superficial appearance, that it feels like my existing intuitions
actively hinder my understanding of what a given statement really does.

The language also feels too "flat" to be easily navigated.
I don't like the idea of a policy language where you need a development environment
and active querying just to reason about it effectively.

IMO it is vital that the experience of navigating and editing policies in a standard bare-bones text
editor be as smooth as possible. If I can't confidently edit access controls in something like nano, thats a problem.

Finally, I'm concerned about the lack of a clear offline "source of truth".
The live/interactive DB model with lots of small facts feels far too dynamic.
Personally, my preference leans toward systems like terraform, where the source of truth for the system
can be easily laid out as a collection of text files that are simple to read and apply.
In a system where individual facts can be injected at-will, it feels as though the end result
would be a mess of "spaghetti policy", with dangling rules and long-forgotten relationships cropping up when you
least expect them. A dangling role isn't such a huge concern in teleport, because the expectation is that
the number of roles is small. A system with hundreds or thousands of single-line free-floating "facts"
seems like a real footgun.

## Appendix C: Data Model - Variant 2

The predicate program compiles to a single WASM file with a program. It provides
some interfaces to query itself, but applying a new variant of the rules means replacing the program.

Each node, proxy and auth server will have a version of the program running.

TODO: Define rollback/versioning, failure modes and scalability of such a system.

## Appendix D. Permission boundaries

[AWS Permission boundaries](https://docs.aws.amazon.com/IAM/latest/UserGuide/access_policies_boundaries.html) can specify maximum boundaries
that identity can operate on. The permissin boundary below limits any holder to only operate on S3, cloudwatch and ec2 even if there is a policy that allows otherwise:


```json
{
    "Version": "2012-10-17",
    "Statement": [
        {
            "Effect": "Allow",
            "Action": [
                "s3:*",
                "cloudwatch:*",
                "ec2:*"
            ],
            "Resource": "*"
        }
    ]
}
```

Predicate won't need a special construct to achieve the same goal:

```prolog
% deny any modification on resource that is not a node
deny(Verb, User, Resource) <-
   contains(Verb, [create, delete, update]),
   ! contains(Resource, ["node"]);
```


## Appendix E: Implementation notes Variant A

TODO: Needs more work

Build a compiled version [rust macro library](https://github.com/ekzhang/crepe). It can be compiled as-is in a WASM module
and loaded to any program. This has a benefit of compilation, unit tests, etc.

One can also build an interpreted version for quick experimentation using similar library, but dynamically.

Load the interpreter state when database updates for internal systems, provide
a small interpreter shell to manipulate the database for fun and debugging (e.g. read-only).

### Developer and Deployment life cycle

Predicate comes with a programming environment - users can create in memory transactional databases
and write full programs in rust before creating new policies.

Users can verify their policies using Z3 SMT solver before commiting them to production.

Users can create policies in "trace" mode that does not apply policies, but logs the result
of their evaluation, so they can push policies to production and observe their possible behavior.

Users can roll out staged deployment of policies, observing their behavior on a subset on the infrastructure.

It should be fun to use Predicate in production and staging.

### Extensions

TODO: work in progress

Users can define custom predicates using web assembly and plug them into the built-in prolog interpreter

```prolog
wasm.time(Stamp); % assigns time to Stamp
```

### Backwards compatibility

TODO: work in progress

Prolog frontend provides a nice way to interface with existing Teleport's objects:

```prolog
% lock alice out of the system for one hour
insert(
  lock(alice), 1h);
```

### Safety

TODO: explore constraints

**Constraints**

Users can use Predicate's constraints to prevent accidental policy applications:

```prolog
% Devs can't be admins
member(U, admin) <-
  !member(U, devs);

% Users from other ogs can't be admins
member(U, admin) <-
   (U.org == "myorg.com");
```

**Type constraints**

Prevent accidental group memberships using type checks

TODO: what other type checks can be there?

```
% Nodes can't be admins
member(U, admins) <-
   !type(U, types.User)
```

**Undeclared atoms and clauses**

Use type checking and undeclared variables to bring safety:

```prolog
% error: member's second type can be only types.Group, not string
member(U, "alice@example.com");

% error: atom devz is undeclared
member(U, devz);

% Experiment devz is a types.Group
atom(devz, types.Group);

% OK
member(U, devz);
```

Predicate programmers will declare clauses signatures that are accepted:

```prolog
clause(allow, ssh, types.String, ...);
```

This will avoid making a mistake and using the wrong clause or signature.

### Static analysis of access policies

TODO: Describe how one would use SMT solver like Z3 similar to Zelkova [1]
to find world-open, weak, or duplicate policies.

### References

* [0] [Zanzibar: Google’s Consistent, Global Authorization System](https://research.google/pubs/pub48190/).
* [1] [Zelkova: Semantic-based Automated Reasoning for AWS Access Policies using SMT](https://d1.awsstatic.com/Security/pdfs/Semantic_Based_Automated_Reasoning_for_AWS_Access_Policies_Using_SMT.pdf)

## Appendix F. Teleport use-cases

TODO: explore all teleport use-cases, role templates, OIDC mappings, access requests,
impersonation in detail.
