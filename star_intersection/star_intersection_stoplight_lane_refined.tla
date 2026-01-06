---- MODULE star_intersection_stoplight_lane_refined ----

(* A refined implementation of a single lane at a star intersection.
   This refinement models the detailed physics of cars: movement, acceleration,
   and braking for both the approaching car and the car in the intersection.

   Each car has:
   - exists: whether the car actually exists
   - moving: whether the car is currently in motion
   - accelerator: whether the accelerator pedal is pressed
   - brake: whether the brake pedal is pressed

   Rules:
   - New car approaching green light: moving=TRUE, accelerator=TRUE
   - New car approaching red light: moving=TRUE, brake=TRUE
   - Braking car can stop moving
   - Switching pedals is a two-step process (both false, then new one true)
   - Can only enter intersection while moving
   - Stopped car tries to switch to accelerator, if light is green or in the intersection
   - Non-moving accelerating car can start moving
   - If light is red, car outside the intersection tries to stop
   - Car retains movement/pedal state when entering intersection
   - Car in intersection tries to accelerate and exit
   - Can only exit while moving *)

VARIABLES
    \* Approaching car state
    outside_exists,
    outside_moving,
    outside_accelerator,
    outside_brake,

    \* Car in intersection state
    inside_exists,
    inside_moving,
    inside_accelerator,
    inside_brake,

    \* Environmental variable
    is_green

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                inside_exists, inside_moving, inside_accelerator, inside_brake>>

Init ==
    /\ outside_exists = FALSE
    /\ outside_moving = FALSE
    /\ outside_accelerator = FALSE
    /\ outside_brake = FALSE
    /\ inside_exists = FALSE
    /\ inside_moving = FALSE
    /\ inside_accelerator = FALSE
    /\ inside_brake = FALSE

\* ========== Approaching car actions ==========

\* A new car approaches the intersection
Approach ==
    /\ ~outside_exists
    /\ outside_exists' = TRUE
    /\ outside_moving' = TRUE
    /\ outside_accelerator' = is_green \* Green light: accelerating
    /\ outside_brake' = ~is_green \* Red light: braking
    /\ UNCHANGED <<inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Approaching car stops moving (only when braking)
OutsideStopMoving ==
    /\ outside_exists
    /\ outside_moving
    /\ outside_brake
    /\ outside_moving' = FALSE
    /\ UNCHANGED <<outside_exists, outside_accelerator, outside_brake,
                   inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Approaching car starts moving (only when accelerating and not already moving)
OutsideStartMoving ==
    /\ outside_exists
    /\ ~outside_moving
    /\ outside_accelerator
    /\ outside_moving' = TRUE
    /\ UNCHANGED <<outside_exists, outside_accelerator, outside_brake,
                   inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Approaching car releases the brake pedal (first step of accelerating)
OutsideReleaseBrake ==
    /\ outside_exists
    /\ is_green
    /\ outside_brake
    /\ outside_brake' = FALSE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator,
                   inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Approaching car releases the accelerator (first step of braking)
OutsideReleaseAccelerator ==
    /\ outside_exists
    /\ ~is_green
    /\ outside_accelerator
    /\ outside_accelerator' = FALSE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_brake,
                   inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Approaching car presses accelerator (when green and foot is not on any pedal)
OutsidePressAccelerator ==
    /\ outside_exists
    /\ ~outside_accelerator
    /\ ~outside_brake
    /\ is_green
    /\ outside_accelerator' = TRUE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_brake,
                   inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Approaching car presses brake (when light is red and foot is not on any pedal)
OutsidePressBrake ==
    /\ outside_exists
    /\ ~outside_accelerator
    /\ ~outside_brake
    /\ ~is_green
    /\ outside_brake' = TRUE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator,
                   inside_exists, inside_moving, inside_accelerator, inside_brake>>

\* Car enters the intersection (can only happen while moving)
Enter ==
    /\ outside_exists
    /\ outside_moving
    /\ ~inside_exists
    /\ is_green
    /\ inside_exists' = TRUE
    /\ inside_moving' = outside_moving
    /\ inside_accelerator' = outside_accelerator
    /\ inside_brake' = outside_brake
    /\ outside_exists' = FALSE
    \* These values don't actually matter, but we FALSE them out for clarity
    /\ outside_moving' = FALSE
    /\ outside_accelerator' = FALSE
    /\ outside_brake' = FALSE

\* ========== Car in intersection actions ==========

\* Car in intersection stops moving (only when braking)
InsideStopMoving ==
    /\ inside_exists
    /\ inside_moving
    /\ inside_brake
    /\ inside_moving' = FALSE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                   inside_exists, inside_accelerator, inside_brake>>

\* Car in intersection starts moving (only when accelerating and not already moving)
InsideStartMoving ==
    /\ inside_exists
    /\ ~inside_moving
    /\ inside_accelerator
    /\ inside_moving' = TRUE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                   inside_exists, inside_accelerator, inside_brake>>

\* Car in intersection releases the brake (to exit)
InsideReleaseBrake ==
    /\ inside_exists
    /\ inside_brake  \* Only release when switching from brake to accelerator
    /\ inside_brake' = FALSE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                   inside_exists, inside_moving, inside_accelerator>>

\* Car in intersection presses accelerator (to exit, if no foot on pedals)
InsidePressAccelerator ==
    /\ inside_exists
    /\ ~inside_accelerator
    /\ ~inside_brake
    /\ inside_accelerator' = TRUE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake,
                   inside_exists, inside_moving, inside_brake>>

\* Car exits the intersection (can only happen while moving)
Exit ==
    /\ inside_exists
    /\ inside_moving
    /\ inside_exists' = FALSE
    \* Values don't matter, but we FALSE them out for clarity
    /\ inside_moving' = FALSE
    /\ inside_accelerator' = FALSE
    /\ inside_brake' = FALSE
    /\ UNCHANGED <<outside_exists, outside_moving, outside_accelerator, outside_brake>>

Next ==
    \/ Approach
    \/ OutsideReleaseAccelerator
    \/ OutsidePressBrake
    \/ OutsideStopMoving
    \/ OutsideReleaseBrake
    \/ OutsidePressAccelerator
    \/ OutsideStartMoving
    \/ Enter
    \/ InsideStopMoving
    \/ InsideReleaseBrake
    \/ InsidePressAccelerator
    \/ InsideStartMoving
    \/ Exit

\* Fairness requirements as specified
Fairness ==
    /\ SF_vars(OutsideReleaseBrake)     \* Car must release brake to switch to accelerator
    /\ SF_vars(OutsidePressAccelerator) \* Stopped car must try to accelerate
    /\ SF_vars(                         \* Accelerating car must start moving
        /\ is_green                     \* And eventually, we do this during the duration where the light is green
        /\ OutsideStartMoving
       )
    /\ SF_vars(Enter)                   \* Must eventually enter when possible
    /\ WF_vars(InsideReleaseBrake)      \* Car in must release brake to switch to accelerator
    /\ WF_vars(InsidePressAccelerator)  \* Car must try to accelerate
    /\ WF_vars(InsideStartMoving)       \* Accelerating car must start moving
    /\ WF_vars(Exit)                    \* Must exit when possible

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
