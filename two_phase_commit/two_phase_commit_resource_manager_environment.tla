---- MODULE two_phase_commit_resource_manager_environment ----

(* The environment of a single resource manager: the transaction manager and
   every other resource manager.  The transaction manager may ask this manager to
   prepare at any time, and sends one decision, which can only be a commit once
   this manager has voted.  inbox and outbox are the resource manager's. *)

CONSTANTS
    PrepareMsg,
    PreparedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    inbox,
    outbox

LOCAL vars == <<inbox>>

Init ==
    inbox = {}

RequestPrepare ==
    inbox' = inbox \cup { PrepareMsg }

Commit ==
    /\ inbox \cap { CommitMsg, AbortMsg } = {}
    /\ PreparedMsg \in outbox
    /\ inbox' = inbox \cup { CommitMsg }

Abort ==
    /\ inbox \cap { CommitMsg, AbortMsg } = {}
    /\ inbox' = inbox \cup { AbortMsg }

Next ==
    \/ RequestPrepare
    \/ Commit
    \/ Abort

Spec == Init /\ [][Next]_vars

====
