---- MODULE intersection_stoplight_composite_trace ----

(* A trace specification that demonstrates a complete happy path through the
   composite stoplight intersection. This trace exercises both the NS and EW
   lanes, showing proper alternation and ensuring no parts of the system can
   be omitted while still claiming to implement the spec.

   The trace shows:
   1. NS car approaches, light turns green, enters, exits, light turns red
   2. EW car approaches, light turns green, enters, exits, light turns red
   3. That brings us back to step 0 for infinite repetition *)

EXTENDS Naturals

VARIABLES
    step,
    ns_inside,
    ns_outside,
    ew_inside,
    ew_outside,
    ns_is_green,
    ew_is_green,
    ns_was_last_green

LOCAL vars == <<step, ns_inside, ns_outside, ew_inside, ew_outside, ns_is_green, ew_is_green, ns_was_last_green>>

Init ==
    /\ step = 0
    /\ ns_inside = FALSE
    /\ ns_outside = FALSE
    /\ ew_inside = FALSE
    /\ ew_outside = FALSE
    /\ ns_is_green = FALSE
    /\ ew_is_green = FALSE
    /\ ns_was_last_green = FALSE  \* NS will go first

Next ==
    (*    │   │
       ───┼───┼─
          │   R
       ───┼─R─┼─  *)

    \/ /\ step = 0
       /\ step' = 1
       /\ ns_outside' = TRUE  \* NS car approaches
       /\ UNCHANGED <<
            ns_inside,
            ew_inside,
            ew_outside,
            ns_is_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │ C │
       ───┼───┼─
          │   R
       ───┼─R─┼─  *)

    \/ /\ step = 1
       /\ step' = 2
       /\ ns_is_green' = TRUE  \* NS light turns green
       /\ ns_was_last_green' = TRUE
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ew_inside,
            ew_outside,
            ew_is_green
          >>

    (*    │ C │
       ───┼───┼─
          │   R
       ───┼─G─┼─  *)

    \/ /\ step = 2
       /\ step' = 3
       /\ ns_inside' = TRUE  \* NS car enters intersection
       /\ ns_outside' = FALSE
       /\ UNCHANGED <<
            ew_inside,
            ew_outside,
            ns_is_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │   │
       ───┼───┼─
          │ C R
       ───┼─G─┼─  *)

    \/ /\ step = 3
       /\ step' = 4
       /\ ns_inside' = FALSE  \* NS car exits intersection
       /\ UNCHANGED <<
            ns_outside,
            ew_inside,
            ew_outside,
            ns_is_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │   │
       ───┼───┼─
          │   R
       ───┼─G─┼─  *)

    \/ /\ step = 4
       /\ step' = 5
       /\ ns_is_green' = FALSE  \* NS light turns red
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ew_inside,
            ew_outside,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │   │
       ───┼───┼─
          │   R
       ───┼─R─┼─  *)

    \/ /\ step = 5
       /\ step' = 6
       /\ ew_outside' = TRUE  \* EW car approaches
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ew_inside,
            ns_is_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │   │
       ───┼───┼─
        C │   R
       ───┼─R─┼─  *)

    \/ /\ step = 6
       /\ step' = 7
       /\ ew_is_green' = TRUE  \* EW light turns green
       /\ ns_was_last_green' = FALSE
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ew_inside,
            ew_outside,
            ns_is_green
          >>

    (*    │   │
       ───┼───┼─
        C │   G
       ───┼─R─┼─  *)

    \/ /\ step = 7
       /\ step' = 8
       /\ ew_inside' = TRUE  \* EW car enters intersection
       /\ ew_outside' = FALSE
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ns_is_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │   │
       ───┼───┼─
          │ C G
       ───┼─R─┼─  *)

    \/ /\ step = 8
       /\ step' = 9
       /\ ew_inside' = FALSE  \* EW car exits intersection
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ew_outside,
            ns_is_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*    │   │
       ───┼───┼─
          │   G
       ───┼─R─┼─  *)

    \/ /\ step = 9
       /\ step' = 0  \* This will bring us back to the start
       /\ ew_is_green' = FALSE  \* EW light turns red
       /\ UNCHANGED <<
            ns_inside,
            ns_outside,
            ew_inside,
            ew_outside,
            ns_is_green,
            ns_was_last_green
          >>

\* Our trace needs to be fair, because our spec is fair
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Composite == INSTANCE intersection_stoplight_composite
RefinesComposite == Composite!Spec

====
