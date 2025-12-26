---- MODULE intersection_stoplight_lane ----

(* A single lane controlled by a stoplight. This module represents one lane
   approaching an intersection. It doesn't care about direction or how many
   other lanes exist - it just tracks whether a vehicle is on approach or
   in the intersection, and responds to the is_green environmental signal.

   Cars can enter the intersection when:
   - A car is outside (on approach)
   - No car is currently inside the intersection from this lane
   - The light is green (is_green = TRUE)

   The is_green variable is environmental - it can be controlled by an
   external component in a composition. *)

VARIABLES
    inside,    \* BOOLEAN: whether a car from this lane is in the intersection
    outside,
    is_green

vars == <<inside, outside>>

Init ==
    /\ inside = FALSE
    /\ outside = FALSE

Approach ==
    /\ outside' = TRUE
    /\ UNCHANGED <<inside, is_green>>

Enter ==
    /\ outside
    /\ ~inside
    /\ is_green
    /\ inside' = TRUE
    /\ outside' = FALSE
    /\ UNCHANGED is_green

Exit ==
    /\ inside
    /\ inside' = FALSE
    /\ UNCHANGED <<outside, is_green>>

Next ==
    \/ Approach
    \/ Enter
    \/ Exit

Fairness ==
    /\ WF_vars(Exit)
    /\ SF_vars(Enter)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
