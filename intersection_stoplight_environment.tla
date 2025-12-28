---- MODULE intersection_stoplight_environment ----

(* Minimal environment specification for a stoplight-controlled intersection.

   This environment spec captures the assumptions about the environment's
   behavior regarding intersection clearing. It has three variables:

   - ns_is_green: TRUE when the NS light is green
   - ew_is_green: TRUE when the EW light is green
   - is_intersection_clear: TRUE when the intersection is clear and safe

   The environment allows:
   - The intersection to clear at any time
   - Cars may enter the intersection when a light is green (either direction)

   Light states are system-controlled *)

VARIABLES
    ns_is_green,
    ew_is_green,
    is_intersection_clear

Init ==
    is_intersection_clear \in BOOLEAN

\* Cars may always leave the intersection, ignoring lights
ClearIntersection ==
    /\ is_intersection_clear' = TRUE
    /\ UNCHANGED <<ns_is_green, ew_is_green>>

\* Cars can only enter if a light is green (we don't care about direction)
CarEnters ==
    /\ ns_is_green \/ ew_is_green
    /\ is_intersection_clear' = FALSE
    /\ UNCHANGED <<ns_is_green, ew_is_green>>

Next ==
    \/ ClearIntersection
    \/ CarEnters

Spec == Init /\ [][Next]_is_intersection_clear

====
