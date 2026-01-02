---- MODULE intersection_stopsign ----

(* A refinement of intersection_abstract that implements stop sign behavior.
   Stop signs enforce a simple rule: whoever arrives first at the intersection
   has the right of way. The ns_arrived_first boolean tracks whether the
   North-South direction arrived before East-West. When no cars are waiting
   outside the intersection, this value is arbitrary and doesn't affect
   behavior.  The `wait` variable does all the heavy lifting for safety, but
   without ns_arrived_first, it would not be fair. *)

VARIABLES
    ns_inside,
    ns_outside,
    ew_inside,
    ew_outside,
    ns_arrived_first,
    wait

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<ns_inside, ns_outside, ew_inside, ew_outside, ns_arrived_first>>

Init ==
    /\ ns_inside = FALSE
    /\ ns_outside = FALSE
    /\ ew_inside = FALSE
    /\ ew_outside = FALSE
    /\ ns_arrived_first \in BOOLEAN  \* Arbitrary when no cars outside
    /\ wait = FALSE

NSApproach ==
    /\ ns_outside' = TRUE
    /\ ns_arrived_first' = (~ew_outside \/ ns_arrived_first)
    /\ UNCHANGED <<ns_inside, ew_inside, ew_outside, wait>>

NSEnter ==
    /\ ns_outside
    /\ ~wait
    /\ ns_arrived_first
    /\ ns_inside' = TRUE
    /\ ns_outside' = FALSE
    \* Can't be wrong, because it's either the other direction's turn, or there's no one there and the value doesn't matter
    /\ ns_arrived_first' = ~ns_arrived_first
    /\ wait' = TRUE
    /\ UNCHANGED <<ew_inside, ew_outside>>

NSExit ==
    /\ ns_inside
    /\ ns_inside' = FALSE
    /\ wait' = FALSE
    /\ UNCHANGED <<ns_outside, ew_inside, ew_outside, ns_arrived_first>>

EWApproach ==
    /\ ew_outside' = TRUE
    /\ ns_arrived_first' = (ns_outside /\ ns_arrived_first)
    /\ UNCHANGED <<ns_inside, ns_outside, ew_inside, wait>>

EWEnter ==
    /\ ew_outside
    /\ ~wait
    /\ ~ns_arrived_first
    /\ ew_inside' = TRUE
    /\ ew_outside' = FALSE
    \* Can't be wrong, because it's either the other direction's turn, or there's no one there and the value doesn't matter
    /\ ns_arrived_first' = ~ns_arrived_first
    /\ wait' = TRUE
    /\ UNCHANGED <<ns_inside, ns_outside>>

EWExit ==
    /\ ew_inside
    /\ ew_inside' = FALSE
    /\ wait' = FALSE
    /\ UNCHANGED <<ns_inside, ns_outside, ew_outside, ns_arrived_first>>

Next ==
    \/ NSApproach
    \/ NSEnter
    \/ NSExit
    \/ EWApproach
    \/ EWEnter
    \/ EWExit

Fairness ==
    /\ WF_vars(NSExit \/ EWExit \/ NSEnter \/ EWEnter)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

(* Refinement mapping: the abstract spec sees the same four variables,
   we just hide ns_arrived_first *)
Abstract == INSTANCE intersection_abstract

(* Refinement property: our spec implements the abstract spec *)
ImplementsAbstract == Abstract!Spec

====
