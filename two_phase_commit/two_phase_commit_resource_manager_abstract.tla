---- MODULE two_phase_commit_resource_manager_abstract ----

(* A single resource manager, taken from the group by giving it one member. *)

CONSTANTS
    \* States
    Working,
    Prepared,
    Committed,
    Aborted,

    \* Messages
    PrepareMsg,
    PreparedMsg,
    RefusedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    state,
    inbox,
    outbox

LOCAL TheResourceManager == 0
LOCAL ResourceManagers == { TheResourceManager }

OneFromN == INSTANCE two_phase_commit_resource_managers_abstract WITH
    ResourceManagers <- ResourceManagers,
    state <- [ rm \in ResourceManagers |-> state ],
    inbox <- [ rm \in ResourceManagers |-> inbox ],
    outbox <- [ rm \in ResourceManagers |-> outbox ]

Spec == OneFromN!Spec

====
