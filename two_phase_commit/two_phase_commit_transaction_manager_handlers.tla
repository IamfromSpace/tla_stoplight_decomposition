---- MODULE two_phase_commit_transaction_manager_handlers ----

(* The handlers behind the transaction manager, as a group.  Each has one inbox
   and one outbox, and every message names the Database or resource manager it
   comes from or goes to; the composite routes them.  A reminder wakes an idle
   handler, which reads the decision.  If there is one, the handler broadcasts
   it forever, since nothing acknowledges it.  If not, it collects votes in
   memory, then writes a commit once it has them all, or an abort at any time,
   and reads the decision back.  A handler can crash at any time, forgetting its
   votes.

   Requests to the Database are SQL, against:
     CREATE TABLE decisions (txn_id TEXT PRIMARY KEY, decision TEXT NOT NULL) STRICT;
   Each is one transaction (BEGIN IMMEDIATE ... COMMIT), and its reply holds the
   rows of its final SELECT. *)

CONSTANTS
    Handlers,
    ResourceManagers,

    \* Handler states
    Idle,
    Reading,
    Collecting,
    Committed,
    Aborted,

    \* Parties
    Database,

    \* SQL
    Insert,
    Select,
    DoNothing,
    Decisions,
    Txn,

    \* Resource manager messages
    PreparedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    state,
    prepared,
    inbox,
    outbox

LOCAL vars == <<state, prepared, outbox>>

\* SELECT * FROM decisions WHERE txn_id = :txn;
SelectDecision ==
    [ statement |-> Select, from |-> Decisions, where |-> [ txn_id |-> Txn ] ]

\* INSERT INTO decisions (txn_id, decision) VALUES (:txn, :decision)
\*   ON CONFLICT DO NOTHING;
InsertDecision(decision) ==
    [ statement |-> Insert,
      into |-> Decisions,
      values |-> [ txn_id |-> Txn, decision |-> decision ],
      on_conflict |-> DoNothing ]

\* Every request reads the decision back, so every reply means the same thing.
ReadDecision == << SelectDecision >>
WriteDecision(decision) == << InsertDecision(decision), SelectDecision >>

TypeOK ==
    /\ state \in [ Handlers -> { Idle, Reading, Collecting, Committed, Aborted } ]
    /\ prepared \in [ Handlers -> SUBSET ResourceManagers ]
    /\ outbox \in [ Handlers -> SUBSET (
            [ recipient : { Database },
              sql : { ReadDecision, WriteDecision(Committed), WriteDecision(Aborted) } ]
                \cup [ recipient : ResourceManagers, message : { CommitMsg, AbortMsg } ]) ]

Init ==
    /\ state = [ handler \in Handlers |-> Idle ]
    /\ prepared = [ handler \in Handlers |-> {} ]
    /\ outbox = [ handler \in Handlers |-> {} ]

Start(handler) ==
    /\ state[handler] = Idle
    /\ state' = [ state EXCEPT ![handler] = Reading ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, sql |-> ReadDecision ] } ]
    /\ UNCHANGED prepared

Collect(handler) ==
    /\ state[handler] = Reading
    /\ [ sender |-> Database, rows |-> {} ] \in inbox[handler]
    /\ state' = [ state EXCEPT ![handler] = Collecting ]
    /\ UNCHANGED <<prepared, outbox>>

Learn(handler) ==
    /\ state[handler] = Reading
    /\ \E reply \in inbox[handler] :
        /\ reply.sender = Database
        /\ \E row \in reply.rows : state' = [ state EXCEPT ![handler] = row.decision ]
    /\ UNCHANGED <<prepared, outbox>>

ReceivePrepared(handler, rm) ==
    /\ state[handler] = Collecting
    /\ [ sender |-> rm, message |-> PreparedMsg ] \in inbox[handler]
    /\ prepared' = [ prepared EXCEPT ![handler] = @ \cup { rm } ]
    /\ UNCHANGED <<state, outbox>>

Commit(handler) ==
    /\ state[handler] = Collecting
    /\ prepared[handler] = ResourceManagers
    /\ state' = [ state EXCEPT ![handler] = Reading ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, sql |-> WriteDecision(Committed) ] } ]
    /\ UNCHANGED prepared

\* On an implicit timeout, or a refusal
Abort(handler) ==
    /\ state[handler] = Collecting
    /\ state' = [ state EXCEPT ![handler] = Reading ]
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> Database, sql |-> WriteDecision(Aborted) ] } ]
    /\ UNCHANGED prepared

Broadcast(handler, rm) ==
    /\ state[handler] \in { Committed, Aborted }
    /\ outbox' = [ outbox EXCEPT ![handler] =
            @ \cup { [ recipient |-> rm,
                       message |-> IF state[handler] = Committed THEN CommitMsg ELSE AbortMsg ] } ]
    /\ UNCHANGED <<state, prepared>>

Crash(handler) ==
    /\ state[handler] # Idle
    /\ state' = [ state EXCEPT ![handler] = Idle ]
    /\ prepared' = [ prepared EXCEPT ![handler] = {} ]
    /\ UNCHANGED outbox

Next ==
    \E handler \in Handlers :
        \/ Start(handler)
        \/ Collect(handler)
        \/ Learn(handler)
        \/ \E rm \in ResourceManagers : ReceivePrepared(handler, rm)
        \/ Commit(handler)
        \/ Abort(handler)
        \/ \E rm \in ResourceManagers : Broadcast(handler, rm)
        \/ Crash(handler)

Spec == Init /\ [][Next]_vars

====
