---- MODULE star_intersection_stoplight_lane_environment ----

(* Minimal environment specification for a single stoplight-controlled lane
   at a star intersection.

   This environment spec captures the assumptions about the environment's
   behavior for a single lane. It has one variable:

   - is_green: TRUE when the light for this lane is green

   The environment allows:
   - The light to turn green at any time
   - The light to turn red at any time

   The is_lane_clear variable is provided by the system (the lane),
   not controlled by the environment. *)

VARIABLES
    is_green,
    is_lane_clear

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<is_green>>

Init ==
    /\ is_green = FALSE

Next ==
    is_green' = ~is_green

Spec == Init /\ [][Next]_vars

====
