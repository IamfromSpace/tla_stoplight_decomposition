---- MODULE two_phase_commit_transaction_manager_refined_in_environment ----

(* The refined transaction manager in its environment, which together implement
   the abstract transaction manager. *)

CONSTANTS
    Handlers,
    ResourceManagers,
    Synchronous,

    \* Handler states
    Idle,
    Reading,
    Collecting,
    Committed,
    Aborted,

    \* Transaction manager states
    Undecided,

    \* Parties
    Database,

    \* SQL keywords
    Insert,
    Select,
    DoNothing,

    \* The transaction's id
    Txn,

    \* Resource manager messages
    PrepareMsg,
    PreparedMsg,
    RefusedMsg,
    CommitMsg,
    AbortMsg,

    \* Responses that aren't messages
    Unavailable,
    Acknowledged

\* TLC only checks assumptions in the module it runs, so this repeats the
\* handlers'.
ASSUME Txn \in STRING

VARIABLES
    \* Refined transaction manager vars
    handler_state,
    handler_prepared,
    handler_outbox,
    db_tables,
    db_outbox,
    adapter_outcomes,

    \* Environment vars
    inbox

TM == INSTANCE two_phase_commit_transaction_manager_refined

Environment == INSTANCE two_phase_commit_transaction_manager_environment WITH
    outbox <- TM!outbox

TMVars == <<handler_state, handler_prepared, handler_outbox, db_tables, db_outbox, adapter_outcomes>>
EnvironmentVars == <<inbox>>

LOCAL vars == <<TMVars, EnvironmentVars>>

TypeOK == TM!TypeOK

Decision ==
    LET key == [ txn_id |-> Txn ]
    IN  IF key \in DOMAIN db_tables["decisions"]
        THEN db_tables["decisions"][key].decision
        ELSE Undecided

Init ==
    /\ TM!Init
    /\ Environment!Init

Next ==
    \/ TM!Next /\ UNCHANGED EnvironmentVars
    \/ Environment!Next /\ UNCHANGED TMVars

Spec == Init /\ [][Next]_vars

\* A decision counts as sent to every resource manager once the database records
\* it, so the handlers' broadcasts are stutters, unless they're bogus.  A
\* resource manager can't tell this from a slow delivery, since it never acts on
\* a missing decision.
AbstractOutbox ==
    [ rm \in ResourceManagers |->
        TM!outbox[rm] \cup
            CASE Decision = Committed -> { CommitMsg }
              [] Decision = Aborted -> { AbortMsg }
              [] Decision = Undecided -> {} ]

\* The votes the handlers remember, or all of them once a handler asks to
\* commit: that request had them all, and can outlive its sender's memory.
AbstractPrepared ==
    IF \E handler \in Handlers :
            [ recipient |-> Database, sql |-> TM!HandlerGroup!WriteDecision(Committed) ]
                \in handler_outbox[handler]
    THEN ResourceManagers
    ELSE UNION { handler_prepared[handler] : handler \in Handlers }

TMAbstract == INSTANCE two_phase_commit_transaction_manager_abstract WITH
    state <- Decision,
    prepared <- AbstractPrepared,
    outbox <- AbstractOutbox

ImplementsAbstractTM == TMAbstract!Spec

HandlerEnvironment == INSTANCE two_phase_commit_transaction_manager_handler_environment WITH
    inbox <- TM!HandlerInbox[TM!SomeHandler],
    outbox <- handler_outbox[TM!SomeHandler],
    decision <- Decision

ClosedSpecRefinesHandlerEnvironment == HandlerEnvironment!Spec

====
