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

in
  symlinkJoin
    { name = "all_specs";
      paths =
        [ star_intersection_abstract
        ];
    }
