---- MODULE star_intersection_stoplight ----

(* A stoplight controller for a star intersection with N one-way streets.
   This module controls traffic lights for N directions with the following behavior:

   - All lights start red
   - When the intersection is clear, and all lights are red, the controller
     turns a light green
   - At any point, a green light can turn red
   - No lanes are eternally ignored (but we don't say specifically how this is
     accomplished)

   The is_intersection_clear variable is environmental - it's provided by
   the composition context and indicates whether the intersection is safe
   to allow another car to enter. *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Directions

VARIABLES
    is_green,
    is_intersection_clear

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<is_green>>

Init ==
    /\ is_green = [ d \in Directions |-> FALSE ]

\* Turn a light green when intersection is clear
TurnGreen(direction) ==
    /\ is_intersection_clear
    /\ \A d \in Directions : ~is_green[d]
    /\ is_green' = [ is_green EXCEPT ![direction] = TRUE ]

\* Turn a light red (we leave why unspecified)
TurnRed ==
    \E direction \in Directions :
        /\ is_green[direction]
        /\ is_green' = [ is_green EXCEPT ![direction] = FALSE ]

Next ==
    \/ \E direction \in Directions : TurnGreen(direction)
    \/ TurnRed

Fairness ==
    /\ \A direction \in Directions : SF_vars(TurnGreen(direction))
    /\ WF_vars(TurnRed)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
