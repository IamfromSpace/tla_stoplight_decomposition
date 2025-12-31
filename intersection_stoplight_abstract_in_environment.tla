---- MODULE intersection_stoplight_abstract_in_environment ----

(* Composition of the abstract stoplight controller with the environment.
   This module composes:
   - intersection_stoplight_abstract (the abstract controller)
   - intersection_stoplight_environment (the environment)

   This composition is mostly for the purpose of state graph generation from
   abstract component definitions, avoiding state explosion while showing the
   key behaviors and interactions between controller and environment.  While
   our refined spec is probably still readable as a state graph, that's not the
   common case, so seeing the abstract rendering is likely to be more helpful.
   *)

VARIABLES
    \* Stoplight controller state
    ns_is_green,
    ew_is_green,
    ns_was_last_green,

    \* Environment state
    is_intersection_clear

StoplightVars == <<ns_is_green, ew_is_green, ns_was_last_green>>
EnvironmentVars == <<is_intersection_clear>>

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<StoplightVars, EnvironmentVars>>

Stoplight == INSTANCE intersection_stoplight_abstract

Environment == INSTANCE intersection_stoplight_environment

Init ==
    /\ Stoplight!Init
    /\ Environment!Init

Next ==
    \/ Stoplight!Next /\ UNCHANGED EnvironmentVars
    \/ Environment!Next /\ UNCHANGED StoplightVars

Fairness ==
    Stoplight!Fairness
    \* Environment is a Safety Property; no Fairness

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

====
