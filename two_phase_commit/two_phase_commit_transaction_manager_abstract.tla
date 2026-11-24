---- MODULE two_phase_commit_transaction_manager_abstract ----

(* The transaction manager of two-phase commit.  inbox belongs to the
   environment, which may send anything.  The manager asks resource managers to
   prepare at any time, since a late request does no harm.  It remembers votes
   from its inbox, and may forget any of them at any time, but only commits
   while it remembers them all.  It aborts on a refusal, or when it times out. *)

CONSTANTS
    ResourceManagers,

    \* States
    Undecided,
    Committed,
    Aborted,

    \* Messages
    PrepareMsg,
    PreparedMsg,
    RefusedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    state,
    prepared,
    inbox,
    outbox

LOCAL vars == <<state, prepared, outbox>>

TypeOK ==
    /\ state \in { Undecided, Committed, Aborted }
    /\ prepared \subseteq ResourceManagers
    /\ outbox \in [ ResourceManagers -> SUBSET { PrepareMsg, CommitMsg, AbortMsg } ]

Init ==
    /\ state = Undecided
    /\ prepared = {}
    /\ outbox = [ rm \in ResourceManagers |-> {} ]

RequestPrepare(rm) ==
    /\ outbox' = [ outbox EXCEPT ![rm] = @ \cup { PrepareMsg } ]
    /\ UNCHANGED <<state, prepared>>

ReceivePrepared(rm) ==
    /\ PreparedMsg \in inbox[rm]
    /\ prepared' = prepared \cup { rm }
    /\ UNCHANGED <<state, outbox>>

Forget ==
    /\ prepared' \in SUBSET prepared
    /\ UNCHANGED <<state, outbox>>

Commit ==
    /\ state = Undecided
    /\ prepared = ResourceManagers
    /\ state' = Committed
    /\ outbox' = [ rm \in ResourceManagers |-> outbox[rm] \cup { CommitMsg } ]
    /\ UNCHANGED prepared

Abort ==
    /\ state = Undecided
    /\ \E rm \in ResourceManagers : RefusedMsg \in inbox[rm]
    /\ state' = Aborted
    /\ outbox' = [ rm \in ResourceManagers |-> outbox[rm] \cup { AbortMsg } ]
    /\ UNCHANGED prepared

Timeout ==
    /\ state = Undecided
    /\ state' = Aborted
    /\ outbox' = [ rm \in ResourceManagers |-> outbox[rm] \cup { AbortMsg } ]
    /\ UNCHANGED prepared

Next ==
    \/ \E rm \in ResourceManagers :
        \/ RequestPrepare(rm)
        \/ ReceivePrepared(rm)
    \/ Forget
    \/ Commit
    \/ Abort
    \/ Timeout

Spec == Init /\ [][Next]_vars

====
