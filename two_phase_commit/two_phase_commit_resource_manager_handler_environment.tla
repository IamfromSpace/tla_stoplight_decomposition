---- MODULE two_phase_commit_resource_manager_handler_environment ----

(* The environment of a single handler: the database, the other handlers, and
   the resource manager's environment.  inbox and outbox are the handler's.  The
   database's state is hidden, and the other handlers only show through it. *)

CONSTANTS
    \* Parties
    Database,
    TransactionManager,

    \* Database requests
    PrepareReq,
    RefuseReq,
    CommitReq,
    AbortReq,

    \* Transaction states
    None,
    InProgress,
    Success,
    Fail,
    Refused,

    \* Resource states
    Compatible,
    Conflicting,
    Locked,

    \* Transaction manager messages
    PrepareMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    inbox,
    outbox,

    \* The database's
    transaction,
    resource

LOCAL vars == <<inbox, transaction, resource>>

Init ==
    /\ inbox = {}
    /\ transaction = None
    /\ resource \in { Compatible, Conflicting }

Received(message) == [ sender |-> TransactionManager, message |-> message ] \in inbox

\* The database's handling of a request, as in its spec
Process(request) ==
    CASE request = PrepareReq ->
            IF transaction = None /\ resource = Compatible
            THEN /\ transaction' = InProgress
                 /\ resource' = Locked
            ELSE UNCHANGED <<transaction, resource>>
      [] request = RefuseReq ->
            /\ IF transaction = None
               THEN transaction' = Refused
               ELSE UNCHANGED transaction
            /\ UNCHANGED resource
      [] request = CommitReq ->
            IF transaction = InProgress
            THEN /\ transaction' = Success
                 /\ resource' \in { Compatible, Conflicting }
            ELSE UNCHANGED <<transaction, resource>>
      [] request = AbortReq ->
            /\ IF transaction \in { None, InProgress }
               THEN transaction' = Fail
               ELSE UNCHANGED transaction
            /\ IF transaction = InProgress
               THEN resource' = Compatible
               ELSE UNCHANGED resource

\* The database processes one of this handler's requests, and replies.
Reply ==
    /\ \E m \in outbox :
        /\ m.recipient = Database
        /\ Process(m.request)
    /\ inbox' = inbox \cup
        { [ sender |-> Database, transaction |-> transaction', resource |-> resource' ] }

\* The database processes another handler's request, which this one never sees.
\* Once asked, another handler can always prepare, and can always refuse, since
\* other transactions can always cause a conflict first.  It only commits or
\* aborts once that's decided.
OtherHandler ==
    /\ \E request \in
            (IF Received(PrepareMsg) THEN { PrepareReq, RefuseReq } ELSE {})
                \cup (IF Received(CommitMsg) THEN { CommitReq } ELSE {})
                \cup (IF Received(AbortMsg) THEN { AbortReq } ELSE {}) :
        Process(request)
    /\ UNCHANGED inbox

\* Other transactions may make ours conflict, or stop doing so, unless we hold
\* the lock.
Flip ==
    /\ resource # Locked
    /\ resource' = IF resource = Compatible THEN Conflicting ELSE Compatible
    /\ UNCHANGED <<inbox, transaction>>

\* The transaction manager may ask to prepare at any time.
RequestPrepare ==
    /\ inbox' = inbox \cup { [ sender |-> TransactionManager, message |-> PrepareMsg ] }
    /\ UNCHANGED <<transaction, resource>>

\* The decision is one message.  A commit needs a vote, and another handler can
\* always vote once the prepare is recorded, but none can before.
Commit ==
    /\ ~Received(CommitMsg)
    /\ ~Received(AbortMsg)
    /\ transaction = InProgress
    /\ inbox' = inbox \cup { [ sender |-> TransactionManager, message |-> CommitMsg ] }
    /\ UNCHANGED <<transaction, resource>>

Abort ==
    /\ ~Received(CommitMsg)
    /\ ~Received(AbortMsg)
    /\ inbox' = inbox \cup { [ sender |-> TransactionManager, message |-> AbortMsg ] }
    /\ UNCHANGED <<transaction, resource>>

Next ==
    \/ Reply
    \/ OtherHandler
    \/ Flip
    \/ RequestPrepare
    \/ Commit
    \/ Abort

Spec == Init /\ [][Next]_vars

====
