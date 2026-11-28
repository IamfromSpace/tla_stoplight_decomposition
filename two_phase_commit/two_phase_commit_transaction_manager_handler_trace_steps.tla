---- MODULE two_phase_commit_transaction_manager_handler_trace_steps ----

(* The steps a handler under test and its fuzzer log, as records named as in the
   Rust trace, which numbers resource managers from zero.  EvalStep is the
   composite's step for one, with the other components unchanged, so it can rule
   a step out as well as replay one. *)

EXTENDS FiniteSets, Naturals, two_phase_commit_transaction_manager_handler_in_environment

\* The resource managers in some order, so the traces' numbers can name them
LOCAL Numbered ==
    CHOOSE numbered \in [ 0..(Cardinality(ResourceManagers) - 1) -> ResourceManagers ] :
        \A rm \in ResourceManagers : \E number \in DOMAIN numbered : numbered[number] = rm

LOCAL ParseResourceManager(number) == Numbered[number]

LOCAL ParseDecision(name) ==
    CASE name = "Committed" -> Committed
      [] name = "Aborted" -> Aborted
      [] name = "None" -> Undecided

LOCAL ParseVote(name) ==
    CASE name = "Prepared" -> PreparedMsg
      [] name = "Refused" -> RefusedMsg

LOCAL DecisionToRows(stored) ==
    IF stored = Undecided THEN {} ELSE { [ txn_id |-> Txn, decision |-> stored ] }

LOCAL ParseRequest(request) ==
    CASE request.kind = "ReadDecision" ->
            [ recipient |-> Database, sql |-> HandlerGroup!ReadDecision ]
      [] request.kind = "WriteDecision" ->
            [ recipient |-> Database,
              sql |-> HandlerGroup!WriteDecision(ParseDecision(request.decision)) ]
      [] request.kind = "Prepare" ->
            [ recipient |-> ParseResourceManager(request.rm), message |-> PrepareMsg ]
      [] request.kind = "Commit" ->
            [ recipient |-> ParseResourceManager(request.rm), message |-> CommitMsg ]
      [] request.kind = "Abort" ->
            [ recipient |-> ParseResourceManager(request.rm), message |-> AbortMsg ]

LOCAL ParseMessage(message) ==
    CASE message.kind = "Vote" ->
            [ sender |-> ParseResourceManager(message.rm), message |-> ParseVote(message.vote) ]
      [] message.kind = "Reply" ->
            [ sender |-> Database, rows |-> DecisionToRows(ParseDecision(message.decision)) ]

LOCAL ParseOutcome(outcome) ==
    CASE outcome.kind = "Received" -> ParseMessage(outcome.message)
      [] outcome.kind = "Unavailable" -> Unavailable
      [] outcome.kind = "Acknowledged" -> Acknowledged

LOCAL EvalHandlerStep(step) ==
    /\ "handler" \in DOMAIN step
    /\ CASE step.handler = "Start" -> HandlerGroup!Start(Handler)
         [] step.handler = "Collect" -> HandlerGroup!Collect(Handler)
         [] step.handler = "Learn" ->
                /\ HandlerGroup!Learn(Handler)
                /\ handler_state'[Handler] = ParseDecision(step.decision)
         [] step.handler = "RequestPrepare" ->
                HandlerGroup!RequestPrepare(Handler, ParseResourceManager(step.rm))
         [] step.handler = "ReceivePrepared" ->
                HandlerGroup!ReceivePrepared(Handler, ParseResourceManager(step.rm))
         [] step.handler = "Commit" -> HandlerGroup!Commit(Handler)
         [] step.handler = "Abort" -> HandlerGroup!Abort(Handler)
         [] step.handler = "Timeout" -> HandlerGroup!Timeout(Handler)
         [] step.handler = "Broadcast" ->
                HandlerGroup!Broadcast(Handler, ParseResourceManager(step.rm))

LOCAL EvalAdapterStep(step) ==
    /\ "environment" \in DOMAIN step
    /\ step.environment = "Pair"
    /\ Adapter!Pair(ParseRequest(step.request), ParseOutcome(step.outcome))

LOCAL EvalEnvironmentStep(step) ==
    /\ "environment" \in DOMAIN step
    /\ step.environment # "Pair"
    /\ CASE step.environment = "Vote" ->
                /\ Environment!Vote(ParseResourceManager(step.rm))
                /\ [ sender |-> ParseResourceManager(step.rm),
                     message |-> ParseVote(step.vote) ] \in inbox'
         [] step.environment = "Decide" ->
                /\ Environment!Decide
                /\ decision' = ParseDecision(step.decision)
                /\ UNCHANGED inbox
         [] step.environment = "Reply" ->
                /\ Environment!Reply
                /\ decision' = ParseDecision(step.decision)

EvalStep(step) ==
    \/ EvalHandlerStep(step) /\ UNCHANGED <<AdapterVars, EnvironmentVars>>
    \/ EvalAdapterStep(step) /\ UNCHANGED <<HandlerVars, EnvironmentVars>>
    \/ EvalEnvironmentStep(step) /\ UNCHANGED <<HandlerVars, AdapterVars>>

====
