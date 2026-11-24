---- MODULE two_phase_commit_resource_managers_abstract ----

(* The resource managers of two-phase commit, as a group.  inbox belongs to the
   environment.  Decisions that don't fit a manager's state are ignored, so the
   environment may send anything. *)

CONSTANTS
    ResourceManagers,

    \* States
    Working,
    Prepared,
    Committed,
    Aborted,

    \* Messages
    PreparedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    state,
    inbox,
    outbox

LOCAL vars == <<state, outbox>>

TypeOK ==
    /\ state \in [ ResourceManagers -> { Working, Prepared, Committed, Aborted } ]
    /\ outbox \in [ ResourceManagers -> SUBSET { PreparedMsg } ]

Init ==
    /\ state = [ rm \in ResourceManagers |-> Working ]
    /\ outbox = [ rm \in ResourceManagers |-> {} ]

Prepare(rm) ==
    /\ state[rm] = Working
    /\ state' = [ state EXCEPT ![rm] = Prepared ]
    /\ outbox' = [ outbox EXCEPT ![rm] = @ \cup { PreparedMsg } ]

ChooseToAbort(rm) ==
    /\ state[rm] = Working
    /\ state' = [ state EXCEPT ![rm] = Aborted ]
    /\ UNCHANGED outbox

ReceiveCommit(rm) ==
    /\ CommitMsg \in inbox[rm]
    /\ state[rm] = Prepared
    /\ state' = [ state EXCEPT ![rm] = Committed ]
    /\ UNCHANGED outbox

ReceiveAbort(rm) ==
    /\ AbortMsg \in inbox[rm]
    /\ state[rm] \in { Working, Prepared }
    /\ state' = [ state EXCEPT ![rm] = Aborted ]
    /\ UNCHANGED outbox

Next ==
    \E rm \in ResourceManagers :
        \/ Prepare(rm)
        \/ ChooseToAbort(rm)
        \/ ReceiveCommit(rm)
        \/ ReceiveAbort(rm)

Spec == Init /\ [][Next]_vars

====
