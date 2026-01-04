---- MODULE star_intersection_stoplight_n_lanes_abstract ----

(* An abstract description of N lanes at a star intersection, each controlled
   by a stoplight. This module represents N lanes approaching an intersection.
   It tracks whether a vehicle is on approach or in the intersection for each
   direction, and responds to the is_green environmental signals.

   Cars can enter the intersection when:
   - A car is outside (on approach) for that direction
   - No car is currently inside the intersection from _the same_ lane
   - The light is green for that direction (is_green[direction] = TRUE)

   The is_green variable is environmental - it will be controlled by an
   external component in a composition.

   This is "abstract" because we don't explain here how the cars work - that
   will come from the refinement/composition.

   NOTE: We need to compose in this module, because it's not possible to use
   INSTANCE over an arbitrary set.  So we can't import a single lane definition
   and compose an arbitrary number (we can for fixed numbers, but this is quite
   inconvenient).  So the composed definition is where the implementation
   lives, and then we can get a single lane definition (in its corresponding
   module) by creating an Instance with just one lane.
   *)

CONSTANTS
    Directions

VARIABLES
    inside,
    outside,
    is_green

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<inside, outside>>

Init ==
    /\ inside = [ d \in Directions |-> FALSE ]
    /\ outside = [ d \in Directions |-> FALSE ]

Approach(direction) ==
    /\ outside' = [ outside EXCEPT ![direction] = TRUE ]
    /\ UNCHANGED <<inside>>

Enter(direction) ==
    /\ outside[direction]
    /\ ~inside[direction]
    /\ is_green[direction]
    /\ inside' = [ inside EXCEPT ![direction] = TRUE ]
    /\ outside' = [ outside EXCEPT ![direction] = FALSE ]

Exit(direction) ==
    /\ inside[direction]
    /\ inside' = [ inside EXCEPT ![direction] = FALSE ]
    /\ UNCHANGED <<outside>>

Next ==
    \E direction \in Directions :
        \/ Approach(direction)
        \/ Enter(direction)
        \/ Exit(direction)

Fairness ==
    /\ WF_vars(\E direction \in Directions : Exit(direction))
    /\ \A direction \in Directions : SF_vars(Enter(direction))

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
