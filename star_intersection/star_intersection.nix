{
  runCommand,
  tlaplus,
  symlinkJoin,
}:
let
  star_intersection_abstract =
    runCommand
      "star_intersection_abstract"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=star_intersection_abstract.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./star_intersection_abstract.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./star_intersection_abstract.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  star_intersection_stoplight_composite =
    runCommand
      "star_intersection_stoplight_composite"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=star_intersection_stoplight_composite.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./star_intersection_stoplight_composite.tla} $SPEC
      cp -L ${./star_intersection_abstract.tla} star_intersection_abstract.tla
      cp -L ${./star_intersection_stoplight.tla} star_intersection_stoplight.tla
      cp -L ${./star_intersection_stoplight_n_lanes_abstract.tla} star_intersection_stoplight_n_lanes_abstract.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./star_intersection_stoplight_composite.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

in
  symlinkJoin
    { name = "all_specs";
      paths =
        [ star_intersection_abstract
          star_intersection_stoplight_composite
        ];
    }
