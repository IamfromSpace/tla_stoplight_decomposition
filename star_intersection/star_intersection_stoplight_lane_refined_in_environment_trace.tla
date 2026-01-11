---- MODULE star_intersection_stoplight_lane_refined_in_environment_trace ----

(* A trace specification demonstrating the refined lane controller
   composed with its environment. This trace shows cars with detailed
   physics (moving, accelerating, braking) going through a single lane.

   The trace shows:
   1. Light turns green
   2. First car approaches (accelerating), enters, exits
   3. Second car approaches (accelerating), enters, exits
   4. Light turns red
   5. Third car approaches (braking), stops
   6. Light turns green
   7. Stopped car releases brake (no pedals), presses accelerator,
      starts moving, enters, continues accelerating, exits
   8. Light turns red, loop back to initial state *)

EXTENDS Naturals

VARIABLES
    step,
    \* Refined lane variables
    outside_exists,
    outside_moving,
    outside_accelerator,
    outside_brake,
    inside_exists,
    inside_moving,
    inside_accelerator,
    inside_brake,
    \* Environment variable
    is_green

LOCAL vars == <<step, outside_exists, outside_moving, outside_accelerator, outside_brake,
                inside_exists, inside_moving, inside_accelerator, inside_brake, is_green>>

Init ==
    /\ step = 0
    /\ outside_exists = FALSE
    /\ outside_moving = FALSE
    /\ outside_accelerator = FALSE
    /\ outside_brake = FALSE
    /\ inside_exists = FALSE
    /\ inside_moving = FALSE
    /\ inside_accelerator = FALSE
    /\ inside_brake = FALSE
    /\ is_green = FALSE

Next ==
    (*  ┌─────┐        ┌─────┐
        │     ├────R───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 0
       /\ step' = 1
       /\ is_green' = TRUE  \* Light turns green
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 1
       /\ step' = 2
       /\ outside_exists' = TRUE  \* Car approaches
       /\ outside_moving' = TRUE
       /\ outside_accelerator' = TRUE
       /\ UNCHANGED <<outside_brake, inside_exists, inside_moving,
                      inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ↑→  ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 2
       /\ step' = 3
       /\ inside_exists' = TRUE  \* Car enters intersection
       /\ inside_moving' = TRUE
       /\ inside_accelerator' = TRUE
       /\ outside_exists' = FALSE
       /\ outside_moving' = FALSE
       /\ outside_accelerator' = FALSE
       /\ UNCHANGED <<outside_brake, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤  ↑→ │
        └─────┘        └─────┘  *)

    \/ /\ step = 3
       /\ step' = 4
       /\ inside_exists' = FALSE  \* Car exits
       /\ inside_moving' = FALSE
       /\ inside_accelerator' = FALSE
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator,
                      outside_brake, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 4
       /\ step' = 5
       /\ outside_exists' = TRUE  \* Second car approaches
       /\ outside_moving' = TRUE
       /\ outside_accelerator' = TRUE
       /\ UNCHANGED <<outside_brake, inside_exists, inside_moving,
                      inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ↑→  ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 5
       /\ step' = 6
       /\ inside_exists' = TRUE  \* Car enters intersection
       /\ inside_moving' = TRUE
       /\ inside_accelerator' = TRUE
       /\ outside_exists' = FALSE
       /\ outside_moving' = FALSE
       /\ outside_accelerator' = FALSE
       /\ UNCHANGED <<outside_brake, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤  ↑→ │
        └─────┘        └─────┘  *)

    \/ /\ step = 6
       /\ step' = 7
       /\ inside_exists' = FALSE  \* Car exits
       /\ inside_moving' = FALSE
       /\ inside_accelerator' = FALSE
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                      inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 7
       /\ step' = 8
       /\ is_green' = FALSE  \* Light turns red
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake>>

    (*  ┌─────┐        ┌─────┐
        │     ├────R───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 8
       /\ step' = 9
       /\ outside_exists' = TRUE  \* Third car approaches (red light, braking)
       /\ outside_moving' = TRUE
       /\ outside_brake' = TRUE
       /\ UNCHANGED <<outside_accelerator, inside_exists, inside_moving,
                      inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ↓→  ├────R───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 9
       /\ step' = 10
       /\ outside_moving' = FALSE  \* Car stops
       /\ UNCHANGED <<outside_exists, outside_accelerator, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ↓•  ├────R───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 10
       /\ step' = 11
       /\ is_green' = TRUE  \* Light turns green
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake>>

    (*  ┌─────┐        ┌─────┐
        │ ↓•  ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 11
       /\ step' = 12
       /\ outside_brake' = FALSE  \* Car releases brake
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator,
                      inside_exists, inside_moving, inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ••  ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 12
       /\ step' = 13
       /\ outside_accelerator' = TRUE  \* Car presses accelerator
       /\ UNCHANGED <<outside_exists, outside_moving, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ↑•  ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 13
       /\ step' = 14
       /\ outside_moving' = TRUE  \* Car starts moving
       /\ UNCHANGED <<outside_exists, outside_accelerator, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │ ↑→  ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 14
       /\ step' = 15
       /\ inside_exists' = TRUE  \* Car enters intersection (still accelerating)
       /\ inside_moving' = TRUE
       /\ inside_accelerator' = TRUE
       /\ outside_exists' = FALSE
       /\ outside_moving' = FALSE
       /\ outside_accelerator' = FALSE
       /\ UNCHANGED <<outside_brake, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤  ↑→ │
        └─────┘        └─────┘  *)

    \/ /\ step = 15
       /\ step' = 16
       /\ inside_exists' = FALSE  \* Car exits
       /\ inside_moving' = FALSE
       /\ inside_accelerator' = FALSE
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator,
                      outside_brake, inside_brake, is_green>>

    (*  ┌─────┐        ┌─────┐
        │     ├────G───┤     │
        └─────┘        └─────┘  *)

    \/ /\ step = 16
       /\ step' = 0  \* Loop back to initial state
       /\ is_green' = FALSE  \* Light turns red
       /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                      inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Fair trace to match the fair spec
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

System == INSTANCE star_intersection_stoplight_lane_refined_in_environment

RefinesSystem == System!Spec

====
