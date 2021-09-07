/* Alice is a user*/
user(alice).

/* Alice is a member of dev group */
member(alice, dev).

/* Any user who's name atom is bob is member of dev */
member(X, dev) :-
    X = bob.


/*
Example above answers only concrete facts, but tests true for conte

?- user(X).
X = alice.

?- member(X, dev).
X = alice 

?- member(bob, dev).
true.
*/
