/* Alice is a user*/
user(alice).

/* Alice is a member of dev group */
member(alice, dev).

/* Group view inherits all members of group dev*/
subgroup(dev, view).

/* User Has permissions of a group */
user_has_permissions(User, Group) :-
    user(User),
    member(User, Group); /* User is a member of a subgroup, OR */
    subgroup(ParentGroup, Group),
    member(User, ParentGroup).


/* Luna is a node */
node(luna).

/* Luna has label env: prod */
label(luna, env, prod).

/* Luna is assigned to dev group */
member(luna, dev).

node(mars).
member(mars, dev).


/* model access requests 2 party approvers with facts*/

/* devs can review requests for group membership admins */
can_review(dev, admin).

/* devs can request admin group membership for 10 hours */
can_request(dev, admin, 10).

/* it takes two approvals from dev to get admin role */
approvals(admin, dev, 2).

/* it takes one rejection from any dev to get admin role */
denies(admin, 1).

/* alice's request req1 is to join group dev for 3 hours */
request(req1, alice, admin, 3).

approval(alice, req1).
approval(alice, req1).

request_approved(ReqId) :-
    request(ReqId, User, TargetGroup, _),
    user(User), /* user is a valid user */
    member(User, MemberGroup), /* user is a member of a group */
    can_request(MemberGroup, TargetGroup, _), /* user of a member group can request target group */
    approvals(TargetGroup, MemberGroup, ApproveCount), /* there is defined number of approvals required*/
    findall(ApprovingUser, (approval(ApprovingUser, ReqId), member(ApprovingGroup, ApprovingUser), can_review(ApprovingGroup, TargetGroup)), ApproveList), /* find all approving users who are member of approving group */
    length(ApproveList, ApproveListLen),
    ApproveListLen >= ApproveCount.
