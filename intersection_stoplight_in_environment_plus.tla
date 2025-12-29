---- MODULE intersection_stoplight_in_environment_plus ----

(* Composition of the refined stoplight controller with E+.
   This module composes:
   - intersection_stoplight (the refined controller with explicit wire signaling)
   - intersection_stoplight_environment_plus (E+, the environment that allows one extra step)

   This composition demonstrates a proof obligation of the decomposition theorem:
   E+ /\ C(RefinedSpec) => C(AbstractSpec)

   Where C(F) is the closure of F (F but without Fairness), the strongest
   safety property implied by F. *)

VARIABLES
    \* Stoplight wire signals
    ns_go_green,
    ns_is_green,
    ew_go_green,
    ew_is_green,

    \* Controller state
    ns_was_last_green,

    \* Environment+ state
    is_intersection_clear,
    s

(* NOTE: We need to redefine instance variables, even though Stoplight!vars and
others are available to us, because otherwise TLC doesn't recognize them as
variables that can be primed, they are just treated as regular values. *)
StoplightVars == <<ns_go_green, ns_is_green, ew_go_green, ew_is_green, ns_was_last_green>>
EnvironmentPlusVars == <<s, is_intersection_clear>>

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<StoplightVars, EnvironmentPlusVars>>

Stoplight == INSTANCE intersection_stoplight

EnvironmentPlus == INSTANCE intersection_stoplight_environment_plus

Init ==
    /\ Stoplight!Init
    /\ EnvironmentPlus!Init

Next ==
    \/ Stoplight!Next /\ UNCHANGED EnvironmentPlusVars
    \/ EnvironmentPlus!Next /\ UNCHANGED StoplightVars

(* NOTE: These are equivalent to `Stoplight!SpecClosed /\ EnvironmentPlus!Spec`
(ignoring interleaving), but TLC cannot handle more than one conjunct of the
form `[][Next]_v` in the specification it checks *)
SpecClosed == Init /\ [][Next]_vars

(* NOTE: The abstract spec's view of "green" is expanded to include lights that
are commanded to go green (go_green) OR are actually green (is_green).  This
allows the controller to update ns_was_last_green asynchronously when
commanding the light (rather than synchronously when it actually turns green),
while still appearing synchronous to the abstract spec. Since we wait for the
is_green acknowledgment before turning the light off, cars are guaranteed to
have a chance to see an actual green light and act during this widest possible
view of green-ness. *)
Abstract == INSTANCE intersection_stoplight_abstract WITH
    ns_is_green <- (ns_go_green \/ ns_is_green),
    ew_is_green <- (ew_go_green \/ ew_is_green)

ClosedImplementsAbstractClosed == Abstract!SpecClosed

====
