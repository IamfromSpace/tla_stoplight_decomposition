---- MODULE two_phase_commit_transaction_manager_abstract ----

(* The transaction manager of two-phase commit.  inbox belongs to the
   environment, which may send anything.  The manager remembers votes from its
   inbox, and may forget any of them at any time, but only commits while it
   remembers them all. *)

CONSTANTS
    ResourceManagers,

    \* States
    Undecided,
    Committed,
    Aborted,

    \* Messages
    PreparedMsg,
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
    /\ outbox \in [ ResourceManagers -> SUBSET { CommitMsg, AbortMsg } ]

Init ==
    /\ state = Undecided
    /\ prepared = {}
    /\ outbox = [ rm \in ResourceManagers |-> {} ]

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
    /\ state' = Aborted
    /\ outbox' = [ rm \in ResourceManagers |-> outbox[rm] \cup { AbortMsg } ]
    /\ UNCHANGED prepared

Next ==
    \/ \E rm \in ResourceManagers : ReceivePrepared(rm)
    \/ Forget
    \/ Commit
    \/ Abort

Fairness ==
    /\ \A rm \in ResourceManagers : WF_vars(ReceivePrepared(rm))
    /\ WF_vars(Commit \/ Abort)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
