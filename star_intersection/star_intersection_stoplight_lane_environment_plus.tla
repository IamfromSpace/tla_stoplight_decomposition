---- MODULE star_intersection_stoplight_lane_environment_plus ----

(* Environment E+ that allows one additional step after E goes false.

   This is used for the decomposition theorem proof where we need to show:
   E+ /\ C(RefinedSpec) => C(AbstractSpec)

   State variable s tracks whether we're in normal E mode (s=0),
   ready to take the extra step (s=1). *)

VARIABLES
    s,
    is_green,
    is_lane_clear

Env == INSTANCE star_intersection_stoplight_lane_environment

(* ~Env!Init and ~Env!Next are not model checkable, so we need to translate
them into forms that are. *)
NotEnvInit ==
    is_green = TRUE \* Starting with green light violates Env!Init

NotEnvNext ==
    is_green' = is_green \* The only thing not allowed is staying the same

Init ==
    \/ /\ s = 0
       /\ Env!Init
    \/ /\ s = 1
       /\ NotEnvInit

Next ==
    /\ s = 0
    /\ \/ Env!Next /\ UNCHANGED s
       \/ NotEnvNext /\ s' = 1

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<s, is_green>>

Spec == Init /\ [][Next]_vars

====
