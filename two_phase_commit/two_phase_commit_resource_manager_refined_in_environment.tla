---- MODULE two_phase_commit_resource_manager_refined_in_environment ----

(* The refined resource manager in its environment, which together implement
   one abstract resource manager. *)

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

    \* Resource manager states
    Working,
    Prepared,
    Committed,
    Aborted,

    \* Transaction manager messages
    PrepareMsg,
    PreparedMsg,
    RefusedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    \* Refined resource manager vars
    handler_state,
    handler_outbox,
    db_transaction,
    db_resource,
    db_outbox,

    \* Environment vars
    inbox

RM == INSTANCE two_phase_commit_resource_manager_refined

Environment == INSTANCE two_phase_commit_resource_manager_environment WITH
    outbox <- RM!outbox

RMVars == <<handler_state, handler_outbox, db_transaction, db_resource, db_outbox>>
EnvironmentVars == <<inbox>>

LOCAL vars == <<RMVars, EnvironmentVars>>

TypeOK == RM!TypeOK

Init ==
    /\ RM!Init
    /\ Environment!Init

Next ==
    \/ RM!Next /\ UNCHANGED EnvironmentVars
    \/ Environment!Next /\ UNCHANGED RMVars

Spec == Init /\ [][Next]_vars

AbstractState ==
    CASE db_transaction = None -> Working
      [] db_transaction = InProgress -> Prepared
      [] db_transaction = Success -> Committed
      [] db_transaction = Fail -> Aborted
      [] db_transaction = Refused -> Aborted

\* A vote or refusal counts as sent once a database reply records it, so the
\* handler's own message is a stutter, unless it's bogus.  The transaction
\* manager can't tell this from a slow delivery, since it never acts on a
\* missing message.
AbstractOutbox ==
    RM!outbox \cup
        { IF reply.transaction = InProgress THEN PreparedMsg ELSE RefusedMsg :
            reply \in { reply \in db_outbox : reply.transaction \in { InProgress, Refused } } }

RMAbstract == INSTANCE two_phase_commit_resource_manager_abstract WITH
    state <- AbstractState,
    outbox <- AbstractOutbox

ImplementsAbstractRM == RMAbstract!Spec

\* Any handler will do, by symmetry
LOCAL SomeHandler == CHOOSE handler \in Handlers : TRUE

HandlerEnvironment == INSTANCE two_phase_commit_resource_manager_handler_environment WITH
    inbox <- RM!HandlerInbox[SomeHandler],
    outbox <- handler_outbox[SomeHandler],
    transaction <- db_transaction,
    resource <- db_resource

ClosedSpecRefinesHandlerEnvironment == HandlerEnvironment!Spec

====
