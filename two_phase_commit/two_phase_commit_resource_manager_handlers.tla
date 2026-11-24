---- MODULE two_phase_commit_resource_manager_handlers ----

(* The handlers behind one resource manager, as a group.  Each has one inbox
   and one outbox, and every message names the Database or TransactionManager
   it comes from or goes to; the composite routes them.  A handler wakes for
   the implicit, always-retried prepare or for a decision in its inbox, and can
   crash at any time.  Only a prepare waits for the database's reply; nothing
   is done with the others, so the handler stops as soon as it sends them. *)

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
    Success,
    Fail,
    Conflicting,

    \* Transaction manager messages
    PreparedMsg,
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
                \cup [ recipient : { TransactionManager }, message : { PreparedMsg } ]) ]

Init ==
    /\ state = [ handler \in Handlers |-> Idle ]
    /\ outbox = [ handler \in Handlers |-> {} ]

Prepare(handler) ==
    /\ state[handler] = Idle
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

AlreadyDecided(handler) ==
    /\ state[handler] = Preparing
    /\ \E reply \in inbox[handler] :
        /\ reply.sender = Database
        /\ reply.transaction \in { Success, Fail }
    /\ state' = [ state EXCEPT ![handler] = Idle ]
    /\ UNCHANGED outbox

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
        \/ AlreadyDecided(handler)
        \/ Crash(handler)

Spec == Init /\ [][Next]_vars

====
