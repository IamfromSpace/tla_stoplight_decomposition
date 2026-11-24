---- MODULE two_phase_commit_transaction_manager_environment ----

(* The environment of the transaction manager: every resource manager.  Each
   votes at most once, yes or no, at any time after it's asked to prepare, even
   after an abort it hasn't seen yet.  inbox and outbox are the transaction
   manager's. *)

CONSTANTS
    ResourceManagers,
    PrepareMsg,
    PreparedMsg,
    RefusedMsg

VARIABLES
    inbox,
    outbox

LOCAL vars == <<inbox>>

Init ==
    inbox = [ rm \in ResourceManagers |-> {} ]

Vote(rm) ==
    /\ PrepareMsg \in outbox[rm]
    /\ inbox[rm] = {}
    /\ \E vote \in { PreparedMsg, RefusedMsg } :
        inbox' = [ inbox EXCEPT ![rm] = { vote } ]

Next ==
    \E rm \in ResourceManagers : Vote(rm)

Spec == Init /\ [][Next]_vars

====
