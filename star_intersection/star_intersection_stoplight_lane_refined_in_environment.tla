---- MODULE star_intersection_stoplight_lane_refined_in_environment ----

(* Composition of the refined lane with its environment.
   This module composes the refined lane implementation with the lane
   environment to show that together they implement the abstract lane
   specification. *)

VARIABLES
    \* Refined lane variables
    outside_exists,
    outside_moving,
    outside_accelerator,
    outside_brake,
    inside_exists,
    inside_moving,
    inside_accelerator,
    inside_brake,

    \* Environment variables
    is_green

Lane == INSTANCE star_intersection_stoplight_lane_refined
Environment ==
    INSTANCE star_intersection_stoplight_lane_environment WITH
        is_lane_clear <- ~inside_exists

LaneVars == <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                     inside_exists, inside_moving, inside_accelerator, inside_brake>>
EnvironmentVars == <<is_green>>

LOCAL vars == <<LaneVars, EnvironmentVars>>

Init ==
    /\ Lane!Init
    /\ Environment!Init

Next ==
    \/ Lane!Next /\ UNCHANGED EnvironmentVars
    \/ Environment!Next /\ UNCHANGED LaneVars

Fairness ==
    Lane!Fairness
    \* Environment is a safety property, it has no Fairness

Spec == Init /\ [][Next]_vars /\ Fairness

LaneAbstract == INSTANCE star_intersection_stoplight_lane_abstract WITH
    outside <- outside_exists,
    inside <- inside_exists,
    is_green <- is_green

ImplementsAbstractLane == LaneAbstract!Spec

====
