---- MODULE two_phase_commit_resource_manager_environment ----

(* The environment of a single resource manager: the transaction manager and
   every other resource manager.  All that reaches this manager is one
   decision, which can only be a commit once this manager has voted.  inbox and
   outbox are the resource manager's. *)

CONSTANTS
    PreparedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    inbox,
    outbox

LOCAL vars == <<inbox>>

Init ==
    inbox = {}

Commit ==
    /\ inbox = {}
    /\ PreparedMsg \in outbox
    /\ inbox' = { CommitMsg }

Abort ==
    /\ inbox = {}
    /\ inbox' = { AbortMsg }

Next ==
    \/ Commit
    \/ Abort

Spec == Init /\ [][Next]_vars

====
