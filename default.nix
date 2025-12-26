let
  pkgs = import ./pinned.nix;
in
  pkgs.runCommand
    "spec"
    {
      buildInputs = [ pkgs.tlaplus ];
    }
    ''
    set -euo pipefail

    SPEC=intersection_abstract.tla
    WORKERS=$(( $(nproc) * 3 / 4 ))
    cp -L ${./intersection_abstract.tla} $SPEC
    mkdir $out
    tlc $SPEC -config ${./intersection_abstract.cfg} -workers $WORKERS | tee $out/$SPEC.log
    ''
