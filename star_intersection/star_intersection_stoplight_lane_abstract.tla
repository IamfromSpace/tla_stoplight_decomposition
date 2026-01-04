---- MODULE star_intersection_stoplight_lane_abstract ----

(* An abstract description of a single lane at a star intersection, controlled
   by a stoplight. It tracks whether a vehicle is on approach or in the
   intersection for each direction, and responds to the is_green environmental
   signals.

   Cars can enter the intersection when:
   - A car is outside (on approach) for that direction
   - No car is currently inside the intersection from _this_ lane
   - The light is green

   The is_green variable is environmental - it will be controlled by an
   external component in a composition.

   This is "abstract" because we don't explain here how the cars work - that
   will come from the refinement/composition. *)

VARIABLES
    inside,
    outside,
    is_green

\* vars don't act like vars when imported as an instance, so we keep them local
LOCAL vars == <<inside, outside>>

(* NOTE: that this spec is from stripping a single lane out of the composite of
   N lanes, rather than building the N lane spec out of N instances of this
   particular spec.  This is partly done out of how TLA+ is best expressed.  We
   can't creates INSTANCES over an arbitrary set, so while it's not hard to
   composed a some fixed number of lanes, it's not syntatically possible to
   compose an arbitrary number across via module imports.  So instead, we do
   the reverse, we create a composition of N lanes, and then limit it to just
   one to get this specification.

   This would be more complicated if there was direct or semi-direct
   interaction between the N entities, for example, if they took note of each
   other entity's state.  That would require some sort of internal dictionary
   of each other direction, in which case we can't just pretend that no other
   entities exist.  Ideally though, state like this only shows up in more
   refined implementations, and can be avoided in the most
   abstract-yet-effective specification. *)
LOCAL TheDirection == 0
LOCAL Directions == { TheDirection }

OneFromN == INSTANCE star_intersection_stoplight_n_lanes_abstract WITH
    Directions <- Directions,
    inside <- [ d \in Directions |-> inside ],
    outside <- [ d \in Directions |-> outside ],
    is_green <- [ d \in Directions |-> is_green ]

SpecClosed == OneFromN!SpecClosed
Spec == OneFromN!Spec

====
