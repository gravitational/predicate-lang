sso_attribute(alice, group, admins).
sso_attribute(alice, group, ssh_devs).
sso_attribute(alice, group, ssh_admin_hello).

role(U, R) :-
    sso_attribute(U, group, Attr),
    re_matchsub("ssh_admin_(?<group>.*)"/a, Attr, Sub, []),
    string_concat("admin-", Sub.group, R).

% Run the query:
% role(alice, Roles).
% Roles = hello.
