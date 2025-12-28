---- MODULE intersection_stoplight_abstract ----

(* An abstract stoplight controller for a two-way intersection.
   This module controls two traffic lights (NS and EW directions) with
   the following behavior:

   - Both lights start red
   - When the intersection is clear, the controller turns green the light
     that was NOT last green (alternating fairness)
   - At any point, a green light can turn red

   The is_intersection_clear variable is environmental - it's provided by
   the composition context and indicates whether the intersection is safe
   to allow another car to enter.

   This module enforces:
   - At most one light is green at a time (mutual exclusion)
   - Lights alternate (ensured via ns_was_last_green) *)

VARIABLES
    ns_is_green,
    ew_is_green,
    ns_was_last_green,  \* BOOLEAN: NS most recently green, meaning EW should be green next (or vice versa)
    is_intersection_clear

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<ns_is_green, ew_is_green, ns_was_last_green>>

Init ==
    /\ ns_is_green = FALSE
    /\ ew_is_green = FALSE
    /\ ns_was_last_green \in BOOLEAN  \* Arbitrary initial value

\* Turn NS light green when intersection is clear and it's NS's turn
TurnNSGreen ==
    /\ is_intersection_clear
    /\ ~ns_is_green
    /\ ~ew_is_green
    /\ ~ns_was_last_green  \* NS was NOT last green, so it's NS's turn
    /\ ns_is_green' = TRUE
    /\ ns_was_last_green' = TRUE  \* Record that NS is now/was green
    /\ UNCHANGED ew_is_green

\* Turn EW light green when intersection is clear and it's EW's turn
TurnEWGreen ==
    /\ is_intersection_clear
    /\ ~ew_is_green
    /\ ~ns_is_green
    /\ ns_was_last_green  \* NS was last green, so it's EW's turn
    /\ ew_is_green' = TRUE
    /\ ns_was_last_green' = FALSE  \* Record that EW is now/was green
    /\ UNCHANGED ns_is_green

\* Turn NS light red (we leave why unspecified)
TurnNSRed ==
    /\ ns_is_green
    /\ ns_is_green' = FALSE
    /\ UNCHANGED <<ew_is_green, ns_was_last_green>>

\* Turn EW light red (we leave why unspecified)
TurnEWRed ==
    /\ ew_is_green
    /\ ew_is_green' = FALSE
    /\ UNCHANGED <<ns_is_green, ns_was_last_green>>

Next ==
    \/ TurnNSGreen
    \/ TurnEWGreen
    \/ TurnNSRed
    \/ TurnEWRed

Fairness ==
    WF_vars(Next)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
