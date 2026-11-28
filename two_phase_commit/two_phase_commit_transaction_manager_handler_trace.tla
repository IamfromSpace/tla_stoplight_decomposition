---- MODULE two_phase_commit_transaction_manager_handler_trace ----

(* Replays traces of a handler under test and its fuzzer through the handler in
   its environment, one logged step at a time.  Each trace starts from Init, and
   stutters once it's done.  A step the composite doesn't allow leaves its replay
   stuck, which TLC reports as a deadlock, so if there's none, every trace is a
   behavior of the composite. *)

EXTENDS Naturals, Sequences, two_phase_commit_transaction_manager_handler_trace_steps

CONSTANTS
    \* A sequence of traces, each a sequence of steps
    Traces

VARIABLES
    trace,
    index

\* TLC rebuilds a substituted constant each time it's used, but evaluates this once
LOCAL CachedTraces == Traces

LOCAL Entry == CachedTraces[trace][index]

LOCAL traceVars == <<trace, index, HandlerVars, AdapterVars, EnvironmentVars>>

TraceInit ==
    /\ trace \in DOMAIN CachedTraces
    /\ index = 1
    /\ Init

TraceNext ==
    \/ /\ index \in DOMAIN CachedTraces[trace]
       /\ EvalStep(Entry)
       /\ index' = index + 1
       /\ UNCHANGED trace
    \/ /\ index = Len(CachedTraces[trace]) + 1
       /\ UNCHANGED traceVars

TraceSpec == TraceInit /\ [][TraceNext]_traceVars

====
