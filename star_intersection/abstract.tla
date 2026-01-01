---- MODULE abstract ----

(* An abstract description of an intersection between N one way streets in a
star pattern.  All streets cross all others.

For example, a three direction intersection might look like this:

    \|/
    /|\

Cars are abstract here, we only track one car outside the intersection at a
time, so we track at most two per direction: one inside and one outside.  Once
cars leave the intersection, we no longer track them.  Cars from different
directions in the intersection simultaneously represents a crash.  In this
spec, cars simply don't do that, for reasons unexplained here.  We'd need to
use a refinement mapping to provide a reason for their behavior, such as a stop
sign or stoplights.  We justify cars traveling the same direction waiting for
one another by the fact that they are following eachother.

Also, our cars act fairly, no direction ends up waiting forever.  Again, we
don't explain here how that's actually accomplished. *)

CONSTANTS
    Directions

VARIABLES
    inside,
    outside

Init ==
    /\ inside = [ x \in Directions |-> FALSE ]
    /\ outside = [ x \in Directions |-> FALSE ]

Approach ==
    \E direction \in Directions :
        /\ outside' = [ outside EXCEPT ![direction] = TRUE ]
        /\ UNCHANGED <<inside>>

Enter(direction) ==
    /\ outside[direction]
    /\ \A other_direction \in (Directions \ { direction }) : ~inside[other_direction]
    /\ outside' = [ outside EXCEPT ![direction] = FALSE ]
    /\ inside' = [ inside EXCEPT ![direction] = TRUE ]

Exit ==
    \E direction \in Directions :
        /\ inside[direction]
        /\ inside' = [ inside EXCEPT ![direction] = FALSE ]
        /\ UNCHANGED <<outside>>

Next ==
    \/ Approach
    \/ \E direction \in Directions : Enter(direction)
    \/ Exit

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<inside, outside>>

Fairness ==
    /\ WF_vars(Exit)
    /\ \A direction \in Directions : SF_vars(Enter(direction))

SpecClosed == Init /\ [][Next]_vars
Spec == SpecClosed /\ Fairness

NoCrash ==
    \A a,b \in Directions :
        (a /= b) => ~(inside[a] /\ inside[b])

NoInfiniteWaiting ==
    \A direction \in Directions :
        outside[direction] ~> ~outside[direction]

====
