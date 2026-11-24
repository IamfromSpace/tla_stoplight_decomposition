---- MODULE two_phase_commit_transaction_manager_handler_environment ----

(* The environment of a single handler: the database, the other handlers, and
   the transaction manager's environment.  inbox and outbox are the handler's.
   All that matters of the database is its decision, since every request reads
   it back.  That's hidden, and the other handlers only show through it. *)

CONSTANTS
    ResourceManagers,

    \* Decisions
    Undecided,
    Committed,
    Aborted,

    \* Parties
    Database,

    \* The transaction's id
    Txn,

    \* Resource manager messages
    PreparedMsg,
    RefusedMsg

VARIABLES
    inbox,
    outbox,

    \* The database's
    decision

LOCAL vars == <<inbox, decision>>

Init ==
    /\ inbox = {}
    /\ decision = Undecided

\* Each resource manager votes at most once, yes or no, at any time, since
\* another handler can always have asked it to prepare.
Vote(rm) ==
    /\ \A vote \in { PreparedMsg, RefusedMsg } : [ sender |-> rm, message |-> vote ] \notin inbox
    /\ \E vote \in { PreparedMsg, RefusedMsg } :
        inbox' = inbox \cup { [ sender |-> rm, message |-> vote ] }
    /\ UNCHANGED decision

\* Some handler's write lands: an abort at any time, or a commit once every
\* resource manager has voted yes, since another handler can always hear them
\* all.
Decide ==
    /\ decision = Undecided
    /\ \/ decision' = Aborted
       \/ /\ \A rm \in ResourceManagers : [ sender |-> rm, message |-> PreparedMsg ] \in inbox
          /\ decision' = Committed

\* The database answers one of this handler's requests with the decision's row,
\* if there is one, perhaps as a write lands.
Reply ==
    /\ \E m \in outbox : m.recipient = Database
    /\ Decide \/ UNCHANGED decision
    /\ inbox' = inbox \cup
        { [ sender |-> Database,
            rows |-> IF decision' = Undecided
                     THEN {}
                     ELSE { [ txn_id |-> Txn, decision |-> decision' ] } ] }

Next ==
    \/ \E rm \in ResourceManagers : Vote(rm)
    \/ Decide /\ UNCHANGED inbox
    \/ Reply

Spec == Init /\ [][Next]_vars

====
