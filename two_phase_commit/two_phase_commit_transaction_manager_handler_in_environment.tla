---- MODULE two_phase_commit_transaction_manager_handler_in_environment ----

(* One handler in its environment, seeing messages only as the outcomes of its
   own requests, through the adapter.  This is what a handler under test and
   its fuzzer make up together. *)

CONSTANTS
    Handler,
    ResourceManagers,

    \* Handler states
    Idle,
    Reading,
    Collecting,
    Committed,
    Aborted,

    \* Decisions
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

    \* Outcomes that aren't messages
    Unavailable,
    Acknowledged

\* TLC only checks assumptions in the module it runs, so this repeats the
\* handlers'.
ASSUME Txn \in STRING

VARIABLES
    \* Handler vars
    handler_state,
    handler_prepared,
    handler_outbox,

    \* Adapter vars
    adapter_outcomes,

    \* Environment vars
    inbox,
    decision

Adapter == INSTANCE two_phase_commit_transaction_manager_handler_environment_sync_adapter WITH
    outbox <- handler_outbox[Handler],
    outcomes <- adapter_outcomes

HandlerGroup == INSTANCE two_phase_commit_transaction_manager_handlers WITH
    Handlers <- { Handler },
    state <- handler_state,
    prepared <- handler_prepared,
    inbox <- [ handler \in { Handler } |-> Adapter!Received ],
    outbox <- handler_outbox

Environment == INSTANCE two_phase_commit_transaction_manager_handler_environment WITH
    outbox <- handler_outbox[Handler]

HandlerVars == <<handler_state, handler_prepared, handler_outbox>>
AdapterVars == <<adapter_outcomes>>
EnvironmentVars == <<inbox, decision>>

LOCAL vars == <<HandlerVars, AdapterVars, EnvironmentVars>>

TypeOK ==
    /\ HandlerGroup!TypeOK
    /\ Adapter!TypeOK

Init ==
    /\ HandlerGroup!Init
    /\ Adapter!Init
    /\ Environment!Init

Next ==
    \/ HandlerGroup!Next /\ UNCHANGED <<AdapterVars, EnvironmentVars>>
    \/ Adapter!Next /\ UNCHANGED <<HandlerVars, EnvironmentVars>>
    \/ Environment!Next /\ UNCHANGED <<HandlerVars, AdapterVars>>

Spec == Init /\ [][Next]_vars

====
