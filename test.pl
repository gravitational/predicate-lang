user(alice).
role(admin).
has_role(alice, admin).

node(luna).
node_has_label(luna, env, prod).

dbnode(mongo).
dbnode_has_label(mongo, env, prod).

allow_ssh(admin, view, env, prod).
deny_ssh(admin, root, env, prod).

can_ssh(User, Principal, Node) :-
    role(Role),
    node(Node),    
    has_role(User, Role),
    node_has_label(Node, LabelKey, LabelVal),
    allow_ssh(Role, Principal, LabelKey, LabelVal),
    not(deny_ssh(Role, Principal, LabelKey, LabelVal)).
