---- MODULE intersection_stoplight_environment_plus ----

(* Environment E+ that allows one additional step after E goes false.

   This is used for the decomposition theorem proof where we need to show:
   E+ /\ C(RefinedSpec) => C(AbstractSpec)

   State variable s tracks whether we're in normal E mode (s=0),
   ready to take the extra step (s=1). *)

VARIABLES
    s,
    ns_is_green,
    ew_is_green,
    is_intersection_clear

Env == INSTANCE intersection_stoplight_environment

(* ~Env!Init and ~Env!Next are not model checkable, so we need to translate
them into forms that are.  We validate their correctness below via automated
theorem proving. *)
NotEnvInit == FALSE \* There is no falsible starting state
NotEnvNext ==
    /\ is_intersection_clear' = FALSE
    /\ \/ ~ns_is_green /\ ~ew_is_green
       \/ is_intersection_clear' = TRUE

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
LOCAL vars == <<s, is_intersection_clear>>

Spec == Init /\ [][Next]_vars

THEOREM ~Env!Init = NotEnvInit
    BY DEF Env!Init, NotEnvInit

THEOREM ~Env!Next = NotEnvNext
    BY DEF Env!Next, Env!ClearIntersection, Env!CarEnters, NotEnvNext

====
