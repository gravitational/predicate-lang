approval(lisa, req).
approval(forrest, req).

approval(forrest, req1).

approval(lisa, req2).
approval(forrest, req2).
approval(bob, req2).

approved(Req) :-
    findall(User, approval(User, Req), List),
    length(List, Len),
    Len >= 2.
