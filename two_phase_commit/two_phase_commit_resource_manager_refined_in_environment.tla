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
    PreparedMsg,
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

\* A vote counts as sent once a database reply records the prepare, so the
\* handler's own vote is a stutter, unless it's bogus.  The transaction manager
\* can't tell this from a slow delivery, since it never acts on a missing vote.
AbstractOutbox ==
    RM!outbox \cup
        (IF \E reply \in db_outbox : reply.transaction = InProgress
         THEN { PreparedMsg }
         ELSE {})

RMAbstract == INSTANCE two_phase_commit_resource_manager_abstract WITH
    state <- AbstractState,
    outbox <- AbstractOutbox

\* Safety only, for now
ImplementsAbstractRM == RMAbstract!SpecClosed

====
