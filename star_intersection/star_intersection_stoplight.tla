---- MODULE star_intersection_stoplight ----

(* A stoplight controller for a star intersection with N one-way streets.
   This module controls traffic lights for N directions with the following behavior:

   - All lights start red
   - The stoplight cycles through directions in a ring pattern
   - When the intersection is clear, the controller turns green the next light
     in the ring after the last green light
   - At any point, a green light can turn red

   The is_intersection_clear variable is environmental - it's provided by
   the composition context and indicates whether the intersection is safe
   to allow another car to enter.

   This module enforces:
   - At most one light is green at a time (mutual exclusion)
   - Lights cycle through directions in a deterministic ring order *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Directions

VARIABLES
    is_green,
    last_green_direction,
    is_intersection_clear

\* Grabbed from community modules
LOCAL IsInjective(f) == \A a,b \in DOMAIN f : f[a] = f[b] => a = b
LOCAL SetToSeq(S) ==
  CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)

\* Helper to get the next direction in the ring
\* We need a deterministic ordering, so we'll use a sequence
LOCAL DirectionSeq == SetToSeq(Directions)

LOCAL NextDirection(direction) ==
    LET idx == CHOOSE i \in 1..Cardinality(Directions) : DirectionSeq[i] = direction
        next_idx == IF idx = Cardinality(Directions) THEN 1 ELSE idx + 1
    IN DirectionSeq[next_idx]

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<is_green, last_green_direction>>

Init ==
    /\ is_green = [ d \in Directions |-> FALSE ]
    /\ last_green_direction \in Directions

\* Turn a light green when intersection is clear and it's that direction's turn
TurnGreen ==
    /\ is_intersection_clear
    /\ ~is_green[last_green_direction]
    /\ last_green_direction' = NextDirection(last_green_direction)
    /\ is_green' = [ is_green EXCEPT ![last_green_direction'] = TRUE ]

\* Turn a light red (we leave why unspecified)
TurnRed ==
    \E direction \in Directions :
        /\ is_green[direction]
        /\ is_green' = [ is_green EXCEPT ![direction] = FALSE ]
        /\ UNCHANGED last_green_direction

Next ==
    \/ TurnGreen
    \/ TurnRed

Fairness ==
    WF_vars(Next)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
