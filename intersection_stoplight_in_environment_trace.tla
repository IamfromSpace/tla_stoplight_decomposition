---- MODULE intersection_stoplight_in_environment_trace ----

(* A trace specification demonstrating the refined stoplight controller
   composed with its environment. This trace shows the asynchronous wire
   protocol between the central controller and the traffic lights.

   The trace shows:
   1. Central commands NS green, light responds, car enters
   2. Central commands NS off (car still in intersection)
   3. NS light responds (car still in intersection, both lights red)
   4. Car exits after all wires are low
   5. Central commands EW green (only after intersection clears), light responds
   6. Loop back to step 1 (skipping car entry/exit for brevity)

   Wire protocol:
   - go_green: Central → Light (command wire)
   - is_green: Light → Central (acknowledgment wire)

   Environment:
   - is_intersection_clear: Cars can enter when lights are green, exit anytime *)

EXTENDS Naturals

VARIABLES
    step,
    \* Wire signals
    ns_go_green,
    ns_is_green,
    ew_go_green,
    ew_is_green,
    \* Controller state
    ns_was_last_green,
    \* Environment state
    is_intersection_clear

LOCAL vars == <<step, ns_go_green, ns_is_green, ew_go_green, ew_is_green,
                ns_was_last_green, is_intersection_clear>>

Init ==
    /\ step = 0
    /\ ns_go_green = FALSE
    /\ ns_is_green = FALSE
    /\ ew_go_green = FALSE
    /\ ew_is_green = FALSE
    /\ ns_was_last_green = FALSE  \* NS will go first
    /\ is_intersection_clear = TRUE

Next ==
    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │    │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [EW] │
           └┬┴─────────┤→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 0
       /\ step' = step + 1
       /\ ns_go_green' = TRUE  \* Central commands NS green
       /\ ns_was_last_green' = TRUE
       /\ UNCHANGED <<
            ns_is_green,
            ew_go_green,
            ew_is_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │    │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [NS] │
           └┰┴─────────┤→     │
            ┗━━━━━━━━━━┥←NS   │
                       └──────┘  *)

    \/ /\ step = 1
       /\ step' = step + 1
       /\ ns_is_green' = TRUE  \* NS light responds: now green
       /\ UNCHANGED <<
            ns_go_green,
            ew_go_green,
            ew_is_green,
            ns_was_last_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │    │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤G├─┼       │ [NS] │
           └┰┶━━━━━━━━━┥→     │
            ┗━━━━━━━━━━┥←NS   │
                       └──────┘  *)

    \/ /\ step = 2
       /\ step' = step + 1
       /\ is_intersection_clear' = FALSE  \* Car enters intersection
       /\ UNCHANGED <<
            ns_go_green,
            ns_is_green,
            ew_go_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │  ╳ │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤G├─┼       │ [NS] │
           └┰┶━━━━━━━━━┥→     │
            ┗━━━━━━━━━━┥←NS   │
                       └──────┘  *)

    \/ /\ step = 3
       /\ step' = step + 1
       /\ ns_go_green' = FALSE  \* Central commands NS off (car STILL in intersection)
       /\ UNCHANGED <<
            ns_is_green,
            ew_go_green,
            ew_is_green,
            ns_was_last_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │  ╳ │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤G├─┼       │ [NS] │
           └┬┶━━━━━━━━━┥→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 4
       /\ step' = step + 1
       /\ ns_is_green' = FALSE  \* NS light responds: now red (car STILL in intersection)
       /\ UNCHANGED <<
            ns_go_green,
            ew_go_green,
            ew_is_green,
            ns_was_last_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │  ╳ │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [NS] │
           └┬┴─────────┤→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 5
       /\ step' = step + 1
       /\ is_intersection_clear' = TRUE  \* Car exits: intersection now clear
       /\ UNCHANGED <<
            ns_go_green,
            ns_is_green,
            ew_go_green,
            ew_is_green,
            ns_was_last_green
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │    │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [NS] │
           └┬┴─────────┤→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 6
       /\ step' = step + 1
       /\ ew_go_green' = TRUE  \* Central commands EW green
       /\ ns_was_last_green' = FALSE
       /\ UNCHANGED <<
            ns_go_green,
            ns_is_green,
            ew_is_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┮━━━━━━┥←EW   │
         │    │R├──────┤→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [EW] │
           └┬┴─────────┤→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 7
       /\ step' = step + 1
       /\ ew_is_green' = TRUE  \* EW light responds: now green
       /\ UNCHANGED <<
            ns_go_green,
            ns_is_green,
            ew_go_green,
            ns_was_last_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┮━━━━━━┥←EW   │
         │    │G┝━━━━━━┥→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [EW] │
           └┬┴─────────┤→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 8
       /\ step' = step + 1
       /\ ew_go_green' = FALSE  \* Central commands EW off
       /\ UNCHANGED <<
            ns_go_green,
            ns_is_green,
            ew_is_green,
            ns_was_last_green,
            is_intersection_clear
          >>

    (*   ┼─────┼       ┌──────┐
         │    ┌┴┬──────┤←EW   │
         │    │G┝━━━━━━┥→     │
         │ ┌─┐└┬┘      │ Ctrl │
         ┼─┤R├─┼       │ [EW] │
           └┬┴─────────┤→     │
            └──────────┤←NS   │
                       └──────┘  *)

    \/ /\ step = 9
       /\ step' = 0
       /\ ew_is_green' = FALSE  \* EW light responds: now red
       /\ UNCHANGED <<
            ns_go_green,
            ns_is_green,
            ew_go_green,
            ns_was_last_green,
            is_intersection_clear
          >>

\* Fair trace matches our fair spec
Trace == Init /\ [][Next]_vars /\ WF_vars(Next)

System == INSTANCE intersection_stoplight_in_environment
RefinesSystem == System!Spec

====
