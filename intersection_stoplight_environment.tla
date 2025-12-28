---- MODULE intersection_stoplight_environment ----

(* Minimal environment specification for a stoplight-controlled intersection.

   This environment spec captures the assumptions about the environment's
   behavior regarding intersection clearing. It has two variables:

   - is_a_light_green: TRUE when at least one light is green
   - is_intersection_clear: TRUE when the intersection is clear and safe

   The environment allows:
   - The intersection to clear at any time (when no light is green)
   - Cars may enter the intersection when a light is green

   Lights state are system-controlled *)

VARIABLES
    is_a_light_green,
    is_intersection_clear

Init ==
    is_intersection_clear \in BOOLEAN

\* Cars may always leave the intersection, ignoring lights
ClearIntersection ==
    /\ is_intersection_clear' = TRUE
    /\ UNCHANGED is_a_light_green

\* Cars can only enter if a light is green (we don't care about direction)
CarEnters ==
    /\ is_a_light_green
    /\ is_intersection_clear' = FALSE
    /\ UNCHANGED is_a_light_green

Next ==
    \/ ClearIntersection
    \/ CarEnters

Spec == Init /\ [][Next]_is_intersection_clear

====
