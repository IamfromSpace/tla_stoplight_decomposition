---- MODULE star_intersection_stoplight_lane_refined_in_environment_plus ----

(* Composition of the refined lane with E+.
   This module composes:
   - star_intersection_stoplight_lane_refined (the refined lane with detailed pedal/motion physics)
   - star_intersection_stoplight_lane_environment_plus (E+, the environment that allows one extra step)

   This composition demonstrates a proof obligation of the decomposition theorem:
   E+ /\ C(RefinedSpec) => C(AbstractSpec)

   Where C(F) is the closure of F (F but without Fairness), the strongest
   safety property implied by F. *)

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

    \* Environment+ variables
    is_green,
    s

(* NOTE: We need to redefine instance variables, even though Lane!vars and
others are available to us, because otherwise TLC doesn't recognize them as
variables that can be primed, they are just treated as regular values. *)
LaneVars == <<outside_exists, outside_moving, outside_accelerator, outside_brake,
              inside_exists, inside_moving, inside_accelerator, inside_brake>>
EnvironmentPlusVars == <<s, is_green>>

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<LaneVars, EnvironmentPlusVars>>

Lane == INSTANCE star_intersection_stoplight_lane_refined

EnvironmentPlus ==
    INSTANCE star_intersection_stoplight_lane_environment_plus WITH
        is_lane_clear <- ~inside_exists

Init ==
    /\ Lane!Init
    /\ EnvironmentPlus!Init

Next ==
    \/ Lane!Next /\ EnvironmentPlus!Next
    \/ Lane!Next /\ UNCHANGED EnvironmentPlusVars
    \/ EnvironmentPlus!Next /\ UNCHANGED LaneVars

(* NOTE: These are equivalent to `Lane!SpecClosed /\ EnvironmentPlus!Spec`, but
TLC cannot handle more than one conjunct of the form `[][Next]_v` in the
specification it checks *)
SpecClosed == Init /\ [][Next]_vars

Abstract == INSTANCE star_intersection_stoplight_lane_abstract WITH
    outside <- outside_exists,
    inside <- inside_exists,
    is_green <- is_green

ClosedImplementsAbstractClosed == Abstract!SpecClosed

====
