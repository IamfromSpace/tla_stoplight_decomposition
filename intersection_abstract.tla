---- MODULE intersection_abstract ----

(* An abstract description of an intersection between two one way streets, one
traveling North-South (ns), and the other traveling East-West (ew).  Cars are
abstract here, we only track one car outside the intersection at a time, so we
track at most two per direction: one inside and one outside.  Once cars leave
the intersection, we no longer track them.  Cars from different directions in
the intersection simultaneously represents a crash.  In this spec, cars simply
don't do that, for reasons unexplained here.  We'd need to use a refinement
mapping to provide a reason for their behavior, such as a stop sign or
stoplights.  We justify cars traveling the same direction waiting for one
another by the fact that they are following eachother. *)

VARIABLES
    ns_inside,
    ns_outside,
    ew_inside,
    ew_outside

Init ==
    /\ ns_inside = FALSE
    /\ ns_outside = FALSE
    /\ ew_inside = FALSE
    /\ ew_outside = FALSE

NSApproach ==
    /\ ns_outside' = TRUE
    /\ UNCHANGED <<ns_inside, ew_inside, ew_outside>>

NSEnter ==
    /\ ns_outside
    /\ ~ns_inside
    /\ ~ew_inside
    /\ ns_inside' = TRUE
    /\ ns_outside' = FALSE
    /\ UNCHANGED <<ew_inside, ew_outside>>

NSExit ==
    /\ ns_inside
    /\ ns_inside' = FALSE
    /\ UNCHANGED <<ns_outside, ew_inside, ew_outside>>

EWApproach ==
    /\ ew_outside' = TRUE
    /\ UNCHANGED <<ns_inside, ns_outside, ew_inside>>

EWEnter ==
    /\ ew_outside
    /\ ~ew_inside
    /\ ~ns_inside
    /\ ew_inside' = TRUE
    /\ ew_outside' = FALSE
    /\ UNCHANGED <<ns_inside, ns_outside>>

EWExit ==
    /\ ew_inside
    /\ ew_inside' = FALSE
    /\ UNCHANGED <<ns_inside, ns_outside, ew_outside>>

Next ==
    \/ NSApproach
    \/ NSEnter
    \/ NSExit
    \/ EWApproach
    \/ EWEnter
    \/ EWExit

vars == <<ns_inside, ns_outside, ew_inside, ew_outside>>

Fairness ==
    /\ WF_vars(NSExit \/ EWExit)
    /\ SF_vars(NSEnter \/ EWEnter)

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

NoCrash ==
    ~(ns_inside /\ ew_inside)

====
