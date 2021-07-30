allow(ssh, alice, luna, dev).
allow(ssh, User, Host, root) :-
    member(User, admins),
    member(Host, db).

member(alice, admins).
