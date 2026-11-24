---- MODULE two_phase_commit_resource_manager_refined ----

(* A resource manager as its handlers and its database, wired together.  Each
   handler's requests reach the database with the handler as their sender, and
   each reply goes back to its recipient.  Every handler sees all of inbox,
   which belongs to the environment, and outbox is everything the handlers send
   the TransactionManager. *)

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

    \* Transaction manager messages
    PreparedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    \* Handler vars
    handler_state,
    handler_outbox,

    \* Database vars
    db_transaction,
    db_resource,
    db_outbox,

    \* Environment vars
    inbox

LOCAL Sent == UNION { handler_outbox[handler] : handler \in Handlers }

outbox == { m.message : m \in { m \in Sent : m.recipient = TransactionManager } }

HandlerInbox ==
    [ handler \in Handlers |->
        { [ sender |-> Database, transaction |-> r.transaction, resource |-> r.resource ] :
            r \in { r \in db_outbox : r.recipient = handler } }
        \cup { [ sender |-> TransactionManager, message |-> m ] : m \in inbox } ]

DBInbox ==
    UNION { { [ sender |-> handler, request |-> m.request ] :
                m \in { m \in handler_outbox[handler] : m.recipient = Database } } :
            handler \in Handlers }

HandlerGroup == INSTANCE two_phase_commit_resource_manager_handlers WITH
    state <- handler_state,
    inbox <- HandlerInbox,
    outbox <- handler_outbox

DB == INSTANCE two_phase_commit_resource_manager_db WITH
    transaction <- db_transaction,
    resource <- db_resource,
    inbox <- DBInbox,
    outbox <- db_outbox

HandlerVars == <<handler_state, handler_outbox>>
DBVars == <<db_transaction, db_resource, db_outbox>>

LOCAL vars == <<HandlerVars, DBVars>>

TypeOK ==
    /\ HandlerGroup!TypeOK
    /\ DB!TypeOK

Init ==
    /\ HandlerGroup!Init
    /\ DB!Init

Next ==
    \/ HandlerGroup!Next /\ UNCHANGED DBVars
    \/ DB!Next /\ UNCHANGED HandlerVars

Spec == Init /\ [][Next]_vars

====
