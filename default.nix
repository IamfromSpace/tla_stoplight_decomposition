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

  intersection_stoplight_composite =
    pkgs.runCommand
      "intersection_stoplight_composite"
      {
        buildInputs = [ pkgs.tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_stoplight_composite.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./intersection_abstract.tla} intersection_abstract.tla
      cp -L ${./intersection_stoplight_lane.tla} intersection_stoplight_lane.tla
      cp -L ${./intersection_stoplight_abstract.tla} intersection_stoplight_abstract.tla
      cp -L ${./intersection_stoplight_environment.tla} intersection_stoplight_environment.tla
      cp -L ${./intersection_stoplight_composite.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./intersection_stoplight_composite.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  intersection_stoplight_composite_trace =
    pkgs.runCommand
      "intersection_stoplight_composite_trace"
      {
        buildInputs = [ pkgs.tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_stoplight_composite_trace.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./intersection_abstract.tla} intersection_abstract.tla
      cp -L ${./intersection_stoplight_lane.tla} intersection_stoplight_lane.tla
      cp -L ${./intersection_stoplight_abstract.tla} intersection_stoplight_abstract.tla
      cp -L ${./intersection_stoplight_environment.tla} intersection_stoplight_environment.tla
      cp -L ${./intersection_stoplight_composite.tla} intersection_stoplight_composite.tla
      cp -L ${./intersection_stoplight_composite_trace.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./intersection_stoplight_composite_trace.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  intersection_stoplight_composite_env =
    pkgs.runCommand
      "intersection_stoplight_composite_env"
      {
        buildInputs = [ pkgs.tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_stoplight_composite.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./intersection_abstract.tla} intersection_abstract.tla
      cp -L ${./intersection_stoplight_lane.tla} intersection_stoplight_lane.tla
      cp -L ${./intersection_stoplight_abstract.tla} intersection_stoplight_abstract.tla
      cp -L ${./intersection_stoplight_environment.tla} intersection_stoplight_environment.tla
      cp -L ${./intersection_stoplight_composite.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./intersection_stoplight_composite_env.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  intersection_stoplight_in_environment =
    pkgs.runCommand
      "intersection_stoplight_in_environment"
      {
        buildInputs = [ pkgs.tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_stoplight_in_environment.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./intersection_stoplight.tla} intersection_stoplight.tla
      cp -L ${./intersection_stoplight_environment.tla} intersection_stoplight_environment.tla
      cp -L ${./intersection_stoplight_abstract.tla} intersection_stoplight_abstract.tla
      cp -L ${./intersection_stoplight_in_environment.tla} $SPEC
      mkdir -p $out/share
      tlc $SPEC -config ${./intersection_stoplight_in_environment.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  intersection_stoplight_environment_plus =
    pkgs.runCommand
      "intersection_stoplight_environment_plus"
      {
        # TODO: Isabelle doesn't seem to work
        buildInputs = [ pkgs.tlaps pkgs.ps pkgs.z3 pkgs.isabelle ];
      }
      ''
      set -euo pipefail

      SPEC=intersection_stoplight_environment_plus.tla
      cp -L ${./intersection_stoplight.tla} intersection_stoplight.tla
      cp -L ${./intersection_stoplight_environment.tla} intersection_stoplight_environment.tla
      cp -L ${./intersection_stoplight_abstract.tla} intersection_stoplight_abstract.tla
      cp -L ${./intersection_stoplight_environment_plus.tla} $SPEC
      mkdir -p $out/share
      tlapm $SPEC | tee $out/share/$SPEC-tlaps.log
      '';
in
  pkgs.symlinkJoin
    { name = "all_specs";
      paths =
        [ intersection_abstract
          intersection_stopsign
          intersection_stoplight_composite
          intersection_stoplight_composite_trace
          intersection_stoplight_composite_env
          intersection_stoplight_in_environment
          intersection_stoplight_environment_plus
        ];
    }
