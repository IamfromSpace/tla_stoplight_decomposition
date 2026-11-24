---- MODULE two_phase_commit_resource_manager_handlers ----

(* The handlers behind one resource manager, as a group.  Each has one inbox
   and one outbox, and every message names the Database or TransactionManager
   it comes from or goes to; the composite routes them.  A handler wakes for a
   request or decision in its inbox, so once asked it can prepare any number of
   times, and it can crash at any time.  Only a prepare waits for the database's
   reply, and answers it with a vote or a refusal; nothing is done with the
   others, so the handler stops as soon as it sends them. *)

CONSTANTS
    Handlers,

    \* Handler states
    Idle,
    Preparing,

    \* Parties
    Database,
    TransactionManager,

    \* Database requests
    PrepareReq,
    RefuseReq,
    CommitReq,
    AbortReq,

    \* Database replies
    None,
    InProgress,
    Refused,
    Conflicting,

    \* Transaction manager messages
    PrepareMsg,
    PreparedMsg,
    RefusedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    state,
    inbox,
    outbox

LOCAL vars == <<state, outbox>>

TypeOK ==
    /\ state \in [ Handlers -> { Idle, Preparing } ]
    /\ outbox \in [ Handlers -> SUBSET (
            [ recipient : { Database }, request : { PrepareReq, RefuseReq, CommitReq, AbortReq } ]
                \cup [ recipient : { TransactionManager }, message : { PreparedMsg, RefusedMsg } ]) ]

Init ==
    /\ state = [ handler \in Handlers |-> Idle ]
    /\ outbox = [ handler \in Handlers |-> {} ]

Prepare(handler) ==
    /\ state[handler] = Idle
    /\ [ sender |-> TransactionManager, message |-> PrepareMsg ] \in inbox[handler]
    /\ state' = [ state EXCEPT ![handler] = Preparing ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, request |-> PrepareReq ] } ]

Commit(handler) ==
    /\ state[handler] = Idle
    /\ [ sender |-> TransactionManager, message |-> CommitMsg ] \in inbox[handler]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, request |-> CommitReq ] } ]
    /\ UNCHANGED state

Abort(handler) ==
    /\ state[handler] = Idle
    /\ [ sender |-> TransactionManager, message |-> AbortMsg ] \in inbox[handler]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, request |-> AbortReq ] } ]
    /\ UNCHANGED state

Vote(handler) ==
    /\ state[handler] = Preparing
    /\ \E reply \in inbox[handler] :
        /\ reply.sender = Database
        /\ reply.transaction = InProgress
    /\ state' = [ state EXCEPT ![handler] = Idle ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> TransactionManager, message |-> PreparedMsg ] } ]

Refuse(handler) ==
    /\ state[handler] = Preparing
    /\ \E reply \in inbox[handler] :
        /\ reply.sender = Database
        /\ reply.transaction = None
        /\ reply.resource = Conflicting
    /\ state' = [ state EXCEPT ![handler] = Idle ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, request |-> RefuseReq ] } ]

ReportRefusal(handler) ==
    /\ state[handler] = Preparing
    /\ \E reply \in inbox[handler] :
        /\ reply.sender = Database
        /\ reply.transaction = Refused
    /\ state' = [ state EXCEPT ![handler] = Idle ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> TransactionManager, message |-> RefusedMsg ] } ]

\* Crash also covers a prepare whose reply shows the transaction is already
\* decided: there's nothing left to do, so the handler just stops.
Crash(handler) ==
    /\ state[handler] # Idle
    /\ state' = [ state EXCEPT ![handler] = Idle ]
    /\ UNCHANGED outbox

Next ==
    \E handler \in Handlers :
        \/ Prepare(handler)
        \/ Commit(handler)
        \/ Abort(handler)
        \/ Vote(handler)
        \/ Refuse(handler)
        \/ ReportRefusal(handler)
        \/ Crash(handler)

Spec == Init /\ [][Next]_vars

====
