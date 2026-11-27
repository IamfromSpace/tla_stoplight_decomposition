---- MODULE two_phase_commit_transaction_manager_refined ----

(* The transaction manager as its handlers and its database, wired together.
   Each handler's requests reach the database with the handler as their sender,
   and each reply goes back to its recipient.  Every handler sees all of inbox,
   which belongs to the environment, and outbox[rm] is everything the handlers
   send rm.  If Synchronous, one handler instead sees messages only as the
   outcomes of its own requests, through an adapter. *)

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

VARIABLES
    \* Handler vars
    handler_state,
    handler_prepared,
    handler_outbox,

    \* Database vars
    db_tables,
    db_outbox,

    \* Adapter vars
    adapter_outcomes,

    \* Environment vars
    inbox

LOCAL Sent == UNION { handler_outbox[handler] : handler \in Handlers }

outbox ==
    [ rm \in ResourceManagers |-> { m.message : m \in { m \in Sent : m.recipient = rm } } ]

HandlerInbox ==
    [ handler \in Handlers |->
        { [ sender |-> Database, rows |-> r.rows ] :
            r \in { r \in db_outbox : r.recipient = handler } }
        \cup UNION { { [ sender |-> rm, message |-> m ] : m \in inbox[rm] } :
            rm \in ResourceManagers } ]

DBInbox ==
    UNION { { [ sender |-> handler, sql |-> m.sql ] :
                m \in { m \in handler_outbox[handler] : m.recipient = Database } } :
            handler \in Handlers }

\* CREATE TABLE decisions (txn_id TEXT PRIMARY KEY, decision TEXT NOT NULL) STRICT;
Schema ==
    [ decisions |-> [ columns |-> { "txn_id", "decision" }, primary_key |-> { "txn_id" } ] ]

\* Any handler will do, by symmetry.  One synchronous handler stands for any
\* number, since each only sees less.
SomeHandler == CHOOSE handler \in Handlers : TRUE

Adapter == INSTANCE two_phase_commit_transaction_manager_handler_environment_sync_adapter WITH
    inbox <- HandlerInbox[SomeHandler],
    outbox <- handler_outbox[SomeHandler],
    outcomes <- adapter_outcomes

HandlerView ==
    IF Synchronous
    THEN [ HandlerInbox EXCEPT ![SomeHandler] = Adapter!Received ]
    ELSE HandlerInbox

HandlerGroup == INSTANCE two_phase_commit_transaction_manager_handlers WITH
    state <- handler_state,
    prepared <- handler_prepared,
    inbox <- HandlerView,
    outbox <- handler_outbox

DB == INSTANCE two_phase_commit_sqlite WITH
    tables <- db_tables,
    inbox <- DBInbox,
    outbox <- db_outbox

HandlerVars == <<handler_state, handler_prepared, handler_outbox>>
DBVars == <<db_tables, db_outbox>>
AdapterVars == <<adapter_outcomes>>

LOCAL vars == <<HandlerVars, DBVars, AdapterVars>>

TypeOK ==
    /\ HandlerGroup!TypeOK
    /\ DB!TypeOK
    /\ Adapter!TypeOK

Init ==
    /\ HandlerGroup!Init
    /\ DB!Init
    /\ Adapter!Init

Next ==
    \/ HandlerGroup!Next /\ UNCHANGED <<DBVars, AdapterVars>>
    \/ DB!Next /\ UNCHANGED <<HandlerVars, AdapterVars>>
    \/ Synchronous /\ Adapter!Next /\ UNCHANGED <<HandlerVars, DBVars>>

Spec == Init /\ [][Next]_vars

====
