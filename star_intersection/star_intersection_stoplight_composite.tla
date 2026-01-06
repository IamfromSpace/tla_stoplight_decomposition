---- MODULE star_intersection_stoplight_composite ----

(* Composition of N stoplight-controlled lanes and a stoplight controller.
   This module composes:
   - One instance of star_intersection_stoplight_n_lanes_abstract (N lanes)
   - One instance of star_intersection_stoplight (the controller)

   The is_intersection_clear signal for the controller is derived from
   whether any cars are inside the intersection from any lane.

   This composition refines star_intersection_abstract, showing that a
   stoplight-controlled N-way star intersection implements the abstract
   star intersection specification. *)

CONSTANTS
    Directions

VARIABLES
    \* Lane vars
    inside,
    outside,

    \* Stoplight controller vars
    is_green

Lanes == INSTANCE star_intersection_stoplight_n_lanes_abstract
    WITH inside <- inside,
         outside <- outside,
         is_green <- is_green

StoplightCtrl == INSTANCE star_intersection_stoplight
    WITH Directions <- Directions,
         is_green <- is_green,
         is_intersection_clear <- \A d \in Directions : ~inside[d]

(* NOTE: We need to redefine instance variables, even though Lanes!vars and
others are available to us, because otherwise TLC doesn't recognize them as
variables that can be primed, they are just treated as regular values. *)
LanesVars == <<inside, outside>>
StoplightCtrlVars == <<is_green>>

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<LanesVars, StoplightCtrlVars>>

Init ==
    /\ Lanes!Init
    /\ StoplightCtrl!Init

Next ==
    (* Non-interleaving part; both components act simultaneously.  Notably, we
    don't really have a good reason to include this intentionally, as
    non-interleaving specifications are mostly just more complicated.  We show
    the more difficult case as an example, should non-interleaving be
    preferrable for some reason. *)
    \/ Lanes!Next /\ StoplightCtrl!Next

    \* Interleaving part, only one component can act per step
    \/ Lanes!Next /\ UNCHANGED StoplightCtrlVars
    \/ StoplightCtrl!Next /\ UNCHANGED LanesVars

Fairness ==
    /\ Lanes!Fairness
    /\ StoplightCtrl!Fairness

(* NOTE: These are equivalent to `Lanes!Spec /\ StoplightCtrl!Spec`, but TLC
cannot handle more than one conjunct of the form `[][Next]_v` in the
specification it checks *)
SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

Abstract == INSTANCE star_intersection_abstract
    WITH inside <- inside,
         outside <- outside,
         Directions <- Directions

ImplementsAbstract == Abstract!Spec

\* Pick an arbitrary direction to check the environment against
LOCAL SomeDirection == CHOOSE d \in Directions : TRUE

LaneEnvironment == INSTANCE star_intersection_stoplight_lane_environment
    WITH is_green <- is_green[SomeDirection],
         are_other_lanes_clear <- \A d \in (Directions \ {SomeDirection}) : ~inside[d],
         is_lane_clear <- ~inside[SomeDirection]

ClosedSpecRefinesLaneEnvironment == LaneEnvironment!Spec

====
