---- MODULE intersection_stoplight_composite ----

(* Composition of two stoplight-controlled lanes and a stoplight controller.
   This module composes:
   - Two instances of intersection_stoplight_lane (NS and EW directions)
   - One instance of intersection_stoplight_abstract (the controller)

   The is_intersection_clear signal for the controller is derived from
   whether any cars are inside the intersection from either lane.

   This composition refines intersection_abstract, showing that a
   stoplight-controlled intersection implements the abstract intersection
   specification. *)

VARIABLES
    \* NS lane vars
    ns_inside,
    ns_outside,

    \* EW lane vars
    ew_inside,
    ew_outside,

    \* Light Vars
    ns_is_green,
    ew_is_green,
    ns_was_last_green

NSLane == INSTANCE intersection_stoplight_lane
    WITH inside <- ns_inside,
         outside <- ns_outside,
         is_green <- ns_is_green

EWLane == INSTANCE intersection_stoplight_lane
    WITH inside <- ew_inside,
         outside <- ew_outside,
         is_green <- ew_is_green

StoplightCtrl == INSTANCE intersection_stoplight_abstract
    WITH is_intersection_clear <- ~ns_inside /\ ~ew_inside

(* NOTE: We need to redefine instance variables, even though EWLane!vars and
others are available to us, because otherwise TLC doesn't recognize them as
variables that can be primed, they are just treated as regular values. *)
EWLaneVars == <<ew_inside, ew_outside>>
NSLaneVars == <<ns_inside, ns_outside>>
StoplightCtrlVars == <<ew_is_green, ns_is_green, ns_was_last_green>>

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<EWLaneVars, NSLaneVars, StoplightCtrlVars>>

Init ==
    /\ NSLane!Init
    /\ EWLane!Init
    /\ StoplightCtrl!Init

Next ==
    \/ NSLane!Next /\ UNCHANGED <<EWLaneVars, StoplightCtrlVars>>
    \/ EWLane!Next /\ UNCHANGED <<NSLaneVars, StoplightCtrlVars>>
    \/ StoplightCtrl!Next /\ UNCHANGED <<NSLaneVars, EWLaneVars>>

Fairness ==
    /\ NSLane!Fairness
    /\ EWLane!Fairness
    /\ StoplightCtrl!Fairness

(* NOTE: These are equivalent to `NSLane!Spec /\ EWLane!Spec /\
StoplightCtrl!Spec` (ignoring interleaving), but TLC cannot handle more than
one conjunct of the form `[][Next]_v` in the specification it checks *)
SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

Abstract == INSTANCE intersection_abstract
ImplementsAbstract == Abstract!Spec

Environment == INSTANCE intersection_stoplight_environment
    WITH is_a_light_green <- ns_is_green \/ ew_is_green,
         is_intersection_clear <- ~ns_inside /\ ~ew_inside

ClosedSpecRefinesStoplightEnvironment == Environment!Spec

====
