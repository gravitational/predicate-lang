% group policies by ID?
policy(mypolicy) :-
    assertz(allow(ssh, alice, dev)),
    assertz(deny(ssh, alice, admin)).



% find all policies
% ?- policy(P).
% P = mypolicy.

% listing(policy(mypolicy)).
% ?- listing(policy(mypolicy)).
% policy(mypolicy) :-
%    assertz(allow(ssh, alice, dev)),
%    assertz(deny(ssh, alice, admin)).
