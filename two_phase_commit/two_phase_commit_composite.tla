---- MODULE two_phase_commit_composite ----

(* The resource managers and transaction manager of two-phase commit, wired
   together.  This refines Lamport's TwoPhase, and so his TCommit. *)

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

\* Interleaving only: a step of both at once isn't a TwoPhase step.
Next ==
    \/ RMs!Next /\ UNCHANGED TMVars
    \/ TM!Next /\ UNCHANGED RMVars

Fairness ==
    /\ RMs!Fairness
    /\ TM!Fairness

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

RMStateName(s) ==
    CASE s = Working -> "working"
      [] s = Prepared -> "prepared"
      [] s = Committed -> "committed"
      [] s = Aborted -> "aborted"

TMStateName(s) ==
    CASE s = Undecided -> "init"
      [] s = Committed -> "committed"
      [] s = Aborted -> "aborted"

TwoPhaseMsgs ==
    LET Voted == { rm \in ResourceManagers : PreparedMsg \in rm_outbox[rm] }
        Decided(msg) == \E rm \in ResourceManagers : msg \in tm_outbox[rm]
    IN  { [ type |-> "Prepared", rm |-> rm ] : rm \in Voted }
            \cup (IF Decided(CommitMsg) THEN { [ type |-> "Commit" ] } ELSE {})
            \cup (IF Decided(AbortMsg) THEN { [ type |-> "Abort" ] } ELSE {})

TwoPhase == INSTANCE TwoPhase
    WITH RM <- ResourceManagers,
         rmState <- [ rm \in ResourceManagers |-> RMStateName(rm_state[rm]) ],
         tmState <- TMStateName(tm_state),
         tmPrepared <- tm_prepared,
         msgs <- TwoPhaseMsgs

ImplementsTwoPhase == TwoPhase!TPSpec
ImplementsTCommit == TwoPhase!TC!TCSpec

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
