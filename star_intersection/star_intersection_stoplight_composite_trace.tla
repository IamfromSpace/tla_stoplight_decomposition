---- MODULE star_intersection_stoplight_composite_trace ----

(* A trace specification demonstrating a complete cycle through the star
   intersection composite with three lanes (X, Y, Z).

   The trace shows:
   1. Multiple cars pass through lane X (2 cars)
   2. While X cars are passing, cars approach and wait at Y and Z
   3. After X finishes, Y gets green and one car passes through
   4. Then Z gets green and one car passes through
   5. Return to initial state (all lights red, all clear)

   This exercises all three lanes and demonstrates proper queuing behavior
   where some lanes wait while others have the green light. *)

EXTENDS Naturals, FiniteSets

CONSTANTS X, Y, Z

Directions == {X, Y, Z}

VARIABLES
    step,
    inside,
    outside,
    is_green

LOCAL vars == <<step, inside, outside, is_green>>

Init ==
    /\ step = 0
    /\ inside = [d \in Directions |-> FALSE]
    /\ outside = [d \in Directions |-> FALSE]
    /\ is_green = [d \in Directions |-> FALSE]

Next ==
    (*  X ─────R─┐   ┌─ Z
        Y ─────R─┼───┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 0
       /\ step' = 1
       /\ outside' = [outside EXCEPT ![X] = TRUE]  \* Car approaches X
       /\ UNCHANGED <<inside, is_green>>

    (*  X ──C──R─┐   ┌─ Z
        Y ─────R─┼───┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 1
       /\ step' = 2
       /\ is_green' = [is_green EXCEPT ![X] = TRUE]  \* X light turns green
       /\ UNCHANGED <<inside, outside>>

    (*  X ──C──G─┐   ┌─ Z
        Y ─────R─┼───┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 2
       /\ step' = 3
       /\ inside' = [inside EXCEPT ![X] = TRUE]  \* X car enters intersection
       /\ outside' = [outside EXCEPT ![X] = FALSE]
       /\ UNCHANGED <<is_green>>

    (*  X ─────G─┐   ┌─ Z
        Y ─────R─┼─X─┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 3
       /\ step' = 4
       /\ outside' = [outside EXCEPT ![Y] = TRUE]  \* Car approaches Y (while X inside)
       /\ UNCHANGED <<inside, is_green>>

    (*  X ─────G─┐   ┌─ Z
        Y ──C──R─┼─X─┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 4
       /\ step' = 5
       /\ inside' = [inside EXCEPT ![X] = FALSE]  \* X car exits
       /\ UNCHANGED <<outside, is_green>>

    (*  X ─────G─┐   ┌─ Z
        Y ──C──R─┼───┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 5
       /\ step' = 6
       /\ outside' = [outside EXCEPT ![X] = TRUE]  \* Another car approaches X
       /\ UNCHANGED <<inside, is_green>>

    (*  X ──C──G─┐   ┌─ Z
        Y ──C──R─┼───┼─ Y
        Z ─────R─┘   └─ X  *)

    \/ /\ step = 6
       /\ step' = 7
       /\ outside' = [outside EXCEPT ![Z] = TRUE]  \* Car approaches Z (while X waiting)
       /\ UNCHANGED <<inside, is_green>>

    (*  X ──C──G─┐   ┌─ Z
        Y ──C──R─┼───┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 7
       /\ step' = 8
       /\ inside' = [inside EXCEPT ![X] = TRUE]  \* Second X car enters (Y, Z waiting)
       /\ outside' = [outside EXCEPT ![X] = FALSE]
       /\ UNCHANGED <<is_green>>

    (*  X ─────G─┐   ┌─ Z
        Y ──C──R─┼─X─┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 8
       /\ step' = 9
       /\ inside' = [inside EXCEPT ![X] = FALSE]  \* Second X car exits
       /\ UNCHANGED <<outside, is_green>>

    (*  X ─────G─┐   ┌─ Z
        Y ──C──R─┼───┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 9
       /\ step' = 10
       /\ is_green' = [is_green EXCEPT ![X] = FALSE]  \* X light turns red
       /\ UNCHANGED <<inside, outside>>

    (*  X ─────R─┐   ┌─ Z
        Y ──C──R─┼───┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 10
       /\ step' = 11
       /\ is_green' = [is_green EXCEPT ![Y] = TRUE]  \* Y light turns green
       /\ UNCHANGED <<inside, outside>>

    (*  X ─────R─┐   ┌─ Z
        Y ──C──G─┼───┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 11
       /\ step' = 12
       /\ inside' = [inside EXCEPT ![Y] = TRUE]  \* Y car enters (Z still waiting)
       /\ outside' = [outside EXCEPT ![Y] = FALSE]
       /\ UNCHANGED <<is_green>>

    (*  X ─────R─┐   ┌─ Z
        Y ─────G─┼─Y─┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 12
       /\ step' = 13
       /\ inside' = [inside EXCEPT ![Y] = FALSE]  \* Y car exits
       /\ UNCHANGED <<outside, is_green>>

    (*  X ─────R─┐   ┌─ Z
        Y ─────G─┼───┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 13
       /\ step' = 14
       /\ is_green' = [is_green EXCEPT ![Y] = FALSE]  \* Y light turns red
       /\ UNCHANGED <<inside, outside>>

    (*  X ─────R─┐   ┌─ Z
        Y ─────R─┼───┼─ Y
        Z ──C──R─┘   └─ X  *)

    \/ /\ step = 14
       /\ step' = 15
       /\ is_green' = [is_green EXCEPT ![Z] = TRUE]  \* Z light turns green
       /\ UNCHANGED <<inside, outside>>

    (*  X ─────R─┐   ┌─ Z
        Y ─────R─┼───┼─ Y
        Z ──C──G─┘   └─ X  *)

    \/ /\ step = 15
       /\ step' = 16
       /\ inside' = [inside EXCEPT ![Z] = TRUE]  \* Z car enters
       /\ outside' = [outside EXCEPT ![Z] = FALSE]
       /\ UNCHANGED <<is_green>>

    (*  X ─────R─┐   ┌─ Z
        Y ─────R─┼─Z─┼─ Y
        Z ─────G─┘   └─ X  *)

    \/ /\ step = 16
       /\ step' = 17
       /\ inside' = [inside EXCEPT ![Z] = FALSE]  \* Z car exits
       /\ UNCHANGED <<outside, is_green>>

    (*  X ─────R─┐   ┌─ Z
        Y ─────R─┼───┼─ Y
        Z ─────G─┘   └─ X  *)

    \/ /\ step = 17
       /\ step' = 0  \* Loop back to initial state
       /\ is_green' = [is_green EXCEPT ![Z] = FALSE]  \* Z light turns red
       /\ UNCHANGED <<inside, outside>>

\* Fair trace to match the fair spec
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Composite == INSTANCE star_intersection_stoplight_composite
    WITH Directions <- Directions,
         inside <- inside,
         outside <- outside,
         is_green <- is_green

RefinesComposite == Composite!Spec

====
