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
in
  pkgs.symlinkJoin
    { name = "all_specs";
      paths =
        [ intersection_abstract
        ];
    }
