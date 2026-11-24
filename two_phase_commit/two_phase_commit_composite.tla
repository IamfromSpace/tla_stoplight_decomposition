---- MODULE two_phase_commit_composite ----

(* The resource managers and transaction manager of two-phase commit, wired
   together.  This refines Lamport's TCommit, but not his TwoPhase, whose
   transaction manager never forgets a vote. *)

CONSTANTS
    ResourceManagers,

    \* States
    Working,
    Prepared,
    Committed,
    Aborted,
    Undecided,

    \* Messages
    PreparedMsg,
    CommitMsg,
    AbortMsg

VARIABLES
    \* Resource manager vars
    rm_state,
    rm_outbox,

    \* Transaction manager vars
    tm_state,
    tm_prepared,
    tm_outbox

RMs == INSTANCE two_phase_commit_resource_managers_abstract
    WITH state <- rm_state,
         inbox <- tm_outbox,
         outbox <- rm_outbox

TM == INSTANCE two_phase_commit_transaction_manager_abstract
    WITH state <- tm_state,
         prepared <- tm_prepared,
         inbox <- rm_outbox,
         outbox <- tm_outbox

RMVars == <<rm_state, rm_outbox>>
TMVars == <<tm_state, tm_prepared, tm_outbox>>

LOCAL vars == <<RMVars, TMVars>>

TypeOK ==
    /\ RMs!TypeOK
    /\ TM!TypeOK

Init ==
    /\ RMs!Init
    /\ TM!Init

Next ==
    \/ RMs!Next /\ UNCHANGED TMVars
    \/ TM!Next /\ UNCHANGED RMVars

Spec == Init /\ [][Next]_vars

RMStateName(s) ==
    CASE s = Working -> "working"
      [] s = Prepared -> "prepared"
      [] s = Committed -> "committed"
      [] s = Aborted -> "aborted"

TCommit == INSTANCE TCommit
    WITH RM <- ResourceManagers,
         rmState <- [ rm \in ResourceManagers |-> RMStateName(rm_state[rm]) ]

ImplementsTCommit == TCommit!TCSpec

\* Any resource manager will do, by symmetry
LOCAL SomeRM == CHOOSE rm \in ResourceManagers : TRUE

RMEnvironment == INSTANCE two_phase_commit_resource_manager_environment
    WITH inbox <- tm_outbox[SomeRM],
         outbox <- rm_outbox[SomeRM]

ClosedSpecRefinesRMEnvironment == RMEnvironment!Spec

TMEnvironment == INSTANCE two_phase_commit_transaction_manager_environment
    WITH inbox <- rm_outbox

ClosedSpecRefinesTMEnvironment == TMEnvironment!Spec

====
