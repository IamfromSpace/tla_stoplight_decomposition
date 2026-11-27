---- MODULE two_phase_commit_transaction_manager_handler_environment_sync_adapter ----

(* Lets a synchronous handler take what its environment sends only as the
   outcomes of its own requests, at most one each.  Any request can fail
   instead.  A request to the database ends with one of its replies, and a
   write only with one showing a decision, since it reads back after inserting.
   A request to prepare ends with the resource manager's vote, and a commit or
   an abort with an acknowledgment.  Failures and acknowledgments aren't
   messages, so the handler never receives them.  The environment is unaware of
   the pairing: inbox is everything it has sent the handler, and outbox
   everything the handler has sent. *)

EXTENDS TLC

CONSTANTS
    \* Parties
    Database,

    \* SQL keywords
    Insert,

    \* Resource manager messages
    PrepareMsg,

    \* Outcomes that aren't messages
    Unavailable,
    Acknowledged

VARIABLES inbox, outbox, outcomes

LOCAL Range(map) == { map[key] : key \in DOMAIN map }

LOCAL Writes(request) == \E statement \in Range(request.sql) : statement.statement = Insert

PossibleOutcomes(request) ==
    { Unavailable } \cup
        IF request.recipient = Database
        THEN { reply \in inbox : reply.sender = Database /\ (Writes(request) => reply.rows # {}) }
        ELSE IF request.message = PrepareMsg
        THEN { vote \in inbox : vote.sender = request.recipient }
        ELSE { Acknowledged }

TypeOK ==
    \A request \in DOMAIN outcomes :
        /\ request \in outbox
        /\ outcomes[request] \in PossibleOutcomes(request)

Received == Range(outcomes) \ { Unavailable, Acknowledged }

Init == outcomes = << >>

Pair(request, outcome) ==
    /\ request \notin DOMAIN outcomes
    /\ outcome \in PossibleOutcomes(request)
    /\ outcomes' = (request :> outcome) @@ outcomes

Next == \E request \in outbox : \E outcome \in PossibleOutcomes(request) : Pair(request, outcome)

Spec == Init /\ [][Next]_outcomes

====
