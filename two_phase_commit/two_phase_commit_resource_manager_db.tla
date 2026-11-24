---- MODULE two_phase_commit_resource_manager_db ----

(* The database behind one resource manager, seen from our one transaction.
   Requests in inbox name their sender and replies in outbox name their
   recipient.  Every write is guarded, so a request can be processed any
   number of times.  The SQL is keyed by :txn and :rid, so it serves any
   number of transactions; <compatible> and <change> stand for the
   application's own check and update. *)

CONSTANTS
    Handlers,

    \* Transaction states
    None,
    InProgress,
    Success,
    Fail,

    \* Resource states.  Conflicting covers both a lock held by another
    \* transaction and data our change can't apply to.
    Compatible,
    Conflicting,
    Locked,

    \* Requests
    PrepareReq,
    RefuseReq,
    CommitReq,
    AbortReq

VARIABLES
    transaction,
    resource,
    inbox,
    outbox

LOCAL vars == <<transaction, resource, outbox>>

TypeOK ==
    /\ transaction \in { None, InProgress, Success, Fail }
    /\ resource \in { Compatible, Conflicting, Locked }
    /\ outbox \subseteq
        [ recipient : Handlers,
          transaction : { None, InProgress, Success, Fail },
          resource : { Compatible, Conflicting, Locked } ]

Init ==
    /\ transaction = None
    /\ resource \in { Compatible, Conflicting }
    /\ outbox = {}

Requested(handler, request) == [ sender |-> handler, request |-> request ] \in inbox

\* Every request is one database transaction that ends by reading back:
\*   SELECT status FROM rm_txns WHERE txn_id = :txn;  -- no row: None
\*   SELECT CASE WHEN locked_by = :txn THEN 'locked'
\*               WHEN locked_by IS NULL AND <compatible> THEN 'compatible'
\*               ELSE 'conflicting' END
\*   FROM resources WHERE id = :rid;
Reply(handler) ==
    outbox' = outbox \cup
        { [ recipient |-> handler, transaction |-> transaction', resource |-> resource' ] }

\* INSERT INTO rm_txns (txn_id, status) VALUES (:txn, 'in_progress')
\*   ON CONFLICT DO NOTHING;
\* UPDATE resources SET locked_by = :txn
\*   WHERE id = :rid AND locked_by IS NULL AND <compatible>;
\* -- ROLLBACK unless both changed a row
Prepare(handler) ==
    /\ Requested(handler, PrepareReq)
    /\ IF transaction = None /\ resource = Compatible
       THEN /\ transaction' = InProgress
            /\ resource' = Locked
       ELSE UNCHANGED <<transaction, resource>>
    /\ Reply(handler)

\* Under snapshot isolation, a failed Prepare writes nothing, so the conflict it
\* reports may be stale and a valid transaction refused: safe, but surprising,
\* and a liveness risk.  Prepare here always sees current state, so snapshot
\* isolation only implements this spec if we explicitly allow stale reads.
\*
\* INSERT INTO rm_txns (txn_id, status) VALUES (:txn, 'fail')
\*   ON CONFLICT DO NOTHING;
Refuse(handler) ==
    /\ Requested(handler, RefuseReq)
    /\ IF transaction = None
       THEN transaction' = Fail
       ELSE UNCHANGED transaction
    /\ UNCHANGED resource
    /\ Reply(handler)

\* UPDATE rm_txns SET status = 'success'
\*   WHERE txn_id = :txn AND status = 'in_progress';
\* UPDATE resources SET <change>, locked_by = NULL
\*   WHERE id = :rid AND locked_by = :txn;
Commit(handler) ==
    /\ Requested(handler, CommitReq)
    /\ IF transaction = InProgress
       THEN /\ transaction' = Success
            /\ resource' \in { Compatible, Conflicting }
       ELSE UNCHANGED <<transaction, resource>>
    /\ Reply(handler)

\* INSERT INTO rm_txns (txn_id, status) VALUES (:txn, 'fail')
\*   ON CONFLICT (txn_id) DO UPDATE SET status = 'fail'
\*   WHERE rm_txns.status = 'in_progress';
\* UPDATE resources SET locked_by = NULL
\*   WHERE id = :rid AND locked_by = :txn;
Abort(handler) ==
    /\ Requested(handler, AbortReq)
    /\ IF transaction \in { None, InProgress }
       THEN transaction' = Fail
       ELSE UNCHANGED transaction
    /\ IF transaction = InProgress
       THEN resource' = Compatible
       ELSE UNCHANGED resource
    /\ Reply(handler)

\* Other transactions may make ours conflict, or stop doing so, unless we hold
\* the lock.
Flip ==
    /\ resource # Locked
    /\ resource' = IF resource = Compatible THEN Conflicting ELSE Compatible
    /\ UNCHANGED <<transaction, outbox>>

Next ==
    \/ \E handler \in Handlers :
        \/ Prepare(handler)
        \/ Refuse(handler)
        \/ Commit(handler)
        \/ Abort(handler)
    \/ Flip

Spec == Init /\ [][Next]_vars

====
