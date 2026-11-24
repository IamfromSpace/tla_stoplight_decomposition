---- MODULE two_phase_commit_transaction_manager_environment ----

(* The environment of the transaction manager: every resource manager.  Each
   votes at most once, at any time, even after an abort it hasn't seen yet.
   inbox is the transaction manager's. *)

CONSTANTS
    ResourceManagers,
    PreparedMsg

VARIABLES
    inbox

LOCAL vars == <<inbox>>

Init ==
    inbox = [ rm \in ResourceManagers |-> {} ]

Vote(rm) ==
    /\ inbox[rm] = {}
    /\ inbox' = [ inbox EXCEPT ![rm] = { PreparedMsg } ]

Next ==
    \E rm \in ResourceManagers : Vote(rm)

Spec == Init /\ [][Next]_vars

====
