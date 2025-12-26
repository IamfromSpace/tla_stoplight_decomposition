let
  pkgs = import ./pinned.nix;

  intersection_abstract =
    pkgs.runCommand
      "intersection_abstract"
      {
        buildInputs = [ pkgs.tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_abstract.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./intersection_abstract.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./intersection_abstract.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  intersection_stopsign =
    pkgs.runCommand
      "intersection_stopsign"
      {
        buildInputs = [ pkgs.tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_stopsign.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./intersection_abstract.tla} intersection_abstract.tla
      cp -L ${./intersection_stopsign.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./intersection_stopsign.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';
in
  pkgs.symlinkJoin
    { name = "all_specs";
      paths =
        [ intersection_abstract
          intersection_stopsign
        ];
    }
