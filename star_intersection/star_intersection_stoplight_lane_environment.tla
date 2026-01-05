---- MODULE star_intersection_stoplight_lane_environment ----

(* Minimal environment specification for a single stoplight-controlled lane
   at a star intersection.

   This environment spec captures the assumptions about the environment's
   behavior for a single lane. It has three variables:

   - is_green: TRUE when the light for this lane is green
   - are_other_lanes_clear: TRUE when all other lanes are clear and safe
   - is_lane_clear: TRUE when this lane itself is clear (no car inside)

   The environment allows:
   - Other lanes to clear at any time (are_other_lanes_clear becomes TRUE)
   - Other lanes to become occupied (are_other_lanes_clear becomes FALSE)
     when the light is not green and this lane is clear
   - The light to turn green when other lanes are clear
   - The light to turn red at any time

   Lane/car state is system-controlled *)

VARIABLES
    is_green,
    are_other_lanes_clear,
    is_lane_clear

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<is_green, are_other_lanes_clear>>

Init ==
    /\ \/ are_other_lanes_clear = TRUE
       \/ are_other_lanes_clear = FALSE
    /\ is_green = FALSE

GoGreen ==
    /\ are_other_lanes_clear = TRUE
    /\ ~is_green
    /\ is_green' = TRUE
    /\ UNCHANGED <<are_other_lanes_clear>>

\* The light can turn red at any point
GoRed ==
    /\ is_green
    /\ is_green' = FALSE
    /\ UNCHANGED <<are_other_lanes_clear>>

\* Other lanes may always clear
OtherLanesClear ==
    /\ are_other_lanes_clear' = TRUE
    /\ UNCHANGED <<is_green>>

\* Other lanes can become occupied when the light is not green and this lane is clear
OtherLanesBecomeOccupied ==
    /\ ~is_green
    /\ is_lane_clear
    /\ are_other_lanes_clear' = FALSE
    /\ UNCHANGED <<is_green>>

Next ==
    \/ GoGreen
    \/ GoRed
    \/ OtherLanesClear
    \/ OtherLanesBecomeOccupied

Spec == Init /\ [][Next]_vars

====
