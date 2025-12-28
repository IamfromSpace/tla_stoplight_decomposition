---- MODULE intersection_stoplight ----

(* A refined stoplight controller with explicit signaling between
   a central controller and two traffic lights (NS and EW).

   The central controller communicates with each light via two wires:
   - go_green: Central tells the light to turn green (input to light)
   - is_green: Light signals it is actually green (output from light)

   All wires start in the low state (FALSE).

   Protocol:
   1. Central raises go_green when intersection is clear and it's that light's turn
   2. Light sees go_green high, turns green, and raises is_green
   3. Central waits for is_green acknowledgment
   4. Central eventually lowers go_green to turn light off
   5. Light sees go_green low, turns red, and lowers is_green
   6. Central waits for is_green to go low, then proceeds to next light

   The central controller alternates between lights using ns_was_last_green. *)

VARIABLES
    \* Wire signals (central <-> NS light)
    ns_go_green,
    ns_is_green,

    \* Wire signals (central <-> EW light)
    ew_go_green,
    ew_is_green,

    \* Central controller state
    ns_was_last_green,

    \* Environmental input
    is_intersection_clear

LOCAL vars == <<ns_go_green, ns_is_green, ew_go_green, ew_is_green, ns_was_last_green>>

Init ==
    /\ ns_go_green = FALSE
    /\ ns_is_green = FALSE
    /\ ew_go_green = FALSE
    /\ ew_is_green = FALSE
    /\ ns_was_last_green \in BOOLEAN

(* ======== Central Controller Actions ======== *)

CentralRequestNSGreen ==
    /\ is_intersection_clear
    /\ ~ns_go_green
    /\ ~ew_go_green
    /\ ~ns_was_last_green  \* It's NS's turn (NS was NOT last green)
    /\ ~ew_is_green \* EW acked the off request
    /\ ns_go_green' = TRUE
    /\ ns_was_last_green' = TRUE  \* Record that NS is now/will be green
    /\ UNCHANGED <<ns_is_green, ew_go_green, ew_is_green, is_intersection_clear>>

CentralRequestEWGreen ==
    /\ is_intersection_clear
    /\ ~ew_go_green
    /\ ~ns_go_green
    /\ ns_was_last_green  \* It's EW's turn (NS was last green)
    /\ ~ns_is_green \* NS acked the off request
    /\ ew_go_green' = TRUE
    /\ ns_was_last_green' = FALSE  \* Record that EW is now/will be green
    /\ UNCHANGED <<ew_is_green, ns_go_green, ns_is_green, is_intersection_clear>>

CentralRequestNSOff ==
    /\ ns_go_green
    /\ ns_is_green  \* Wait for light to acknowledge it's on before requesting off
    /\ ns_go_green' = FALSE
    /\ UNCHANGED <<ns_is_green, ew_go_green, ew_is_green, ns_was_last_green, is_intersection_clear>>

CentralRequestEWOff ==
    /\ ew_go_green
    /\ ew_is_green  \* Wait for light to acknowledge it's on before requesting off
    /\ ew_go_green' = FALSE
    /\ UNCHANGED <<ew_is_green, ns_go_green, ns_is_green, ns_was_last_green, is_intersection_clear>>

(* ======== Light Actions ======== *)

\* NS light takes on the state indicated by the central controller
NSLightFollowCentral ==
    /\ ns_is_green' = ns_go_green
    /\ UNCHANGED <<ns_go_green, ew_go_green, ew_is_green, ns_was_last_green, is_intersection_clear>>

\* EW light takes on the state indicated by the central controller
EWLightFollowCentral ==
    /\ ew_is_green' = ew_go_green
    /\ UNCHANGED <<ns_go_green, ns_is_green, ew_go_green, ns_was_last_green, is_intersection_clear>>

Next ==
    \/ CentralRequestNSGreen
    \/ CentralRequestEWGreen
    \/ CentralRequestNSOff
    \/ CentralRequestEWOff
    \/ NSLightFollowCentral
    \/ EWLightFollowCentral

Fairness ==
    WF_vars(Next)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
