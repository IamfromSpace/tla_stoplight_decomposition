{
  runCommand,
  tlaplus,
  fetchurl,
  symlinkJoin,
}:
let
  tlaplus_examples = "https://raw.githubusercontent.com/tlaplus/Examples/334c3983a2f44ac78fce89d1d20aa79ceb3e6987/specifications/transaction_commit";

  t_commit = fetchurl {
    url = "${tlaplus_examples}/TCommit.tla";
    hash = "sha256-mJdNjF7gB/T2IYhzfCDH3NsFrwmcxTpZyLhlEzH9kl0=";
  };

  two_phase_commit_composite =
    runCommand
      "two_phase_commit_composite"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=two_phase_commit_composite.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./two_phase_commit_composite.tla} $SPEC
      cp -L ${./two_phase_commit_resource_managers_abstract.tla} two_phase_commit_resource_managers_abstract.tla
      cp -L ${./two_phase_commit_transaction_manager_abstract.tla} two_phase_commit_transaction_manager_abstract.tla
      cp -L ${./two_phase_commit_resource_manager_environment.tla} two_phase_commit_resource_manager_environment.tla
      cp -L ${./two_phase_commit_transaction_manager_environment.tla} two_phase_commit_transaction_manager_environment.tla
      cp -L ${t_commit} TCommit.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./two_phase_commit_composite.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  two_phase_commit_resource_manager_refined_in_environment =
    runCommand
      "two_phase_commit_resource_manager_refined_in_environment"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=two_phase_commit_resource_manager_refined_in_environment.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./two_phase_commit_resource_manager_refined_in_environment.tla} $SPEC
      cp -L ${./two_phase_commit_resource_manager_refined.tla} two_phase_commit_resource_manager_refined.tla
      cp -L ${./two_phase_commit_resource_manager_handlers.tla} two_phase_commit_resource_manager_handlers.tla
      cp -L ${./two_phase_commit_resource_manager_db.tla} two_phase_commit_resource_manager_db.tla
      cp -L ${./two_phase_commit_resource_manager_environment.tla} two_phase_commit_resource_manager_environment.tla
      cp -L ${./two_phase_commit_resource_manager_handler_environment.tla} two_phase_commit_resource_manager_handler_environment.tla
      cp -L ${./two_phase_commit_resource_manager_abstract.tla} two_phase_commit_resource_manager_abstract.tla
      cp -L ${./two_phase_commit_resource_managers_abstract.tla} two_phase_commit_resource_managers_abstract.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./two_phase_commit_resource_manager_refined_in_environment.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  two_phase_commit_transaction_manager_refined_in_environment =
    runCommand
      "two_phase_commit_transaction_manager_refined_in_environment"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=two_phase_commit_transaction_manager_refined_in_environment.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./two_phase_commit_transaction_manager_refined_in_environment.tla} $SPEC
      cp -L ${./two_phase_commit_transaction_manager_refined.tla} two_phase_commit_transaction_manager_refined.tla
      cp -L ${./two_phase_commit_transaction_manager_handlers.tla} two_phase_commit_transaction_manager_handlers.tla
      cp -L ${./two_phase_commit_sqlite.tla} two_phase_commit_sqlite.tla
      cp -L ${./two_phase_commit_transaction_manager_environment.tla} two_phase_commit_transaction_manager_environment.tla
      cp -L ${./two_phase_commit_transaction_manager_handler_environment.tla} two_phase_commit_transaction_manager_handler_environment.tla
      cp -L ${./two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla} two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla
      cp -L ${./two_phase_commit_transaction_manager_abstract.tla} two_phase_commit_transaction_manager_abstract.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./two_phase_commit_transaction_manager_refined_in_environment.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

  two_phase_commit_transaction_manager_refined_in_environment_sync =
    runCommand
      "two_phase_commit_transaction_manager_refined_in_environment_sync"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=two_phase_commit_transaction_manager_refined_in_environment.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./two_phase_commit_transaction_manager_refined_in_environment.tla} $SPEC
      cp -L ${./two_phase_commit_transaction_manager_refined.tla} two_phase_commit_transaction_manager_refined.tla
      cp -L ${./two_phase_commit_transaction_manager_handlers.tla} two_phase_commit_transaction_manager_handlers.tla
      cp -L ${./two_phase_commit_sqlite.tla} two_phase_commit_sqlite.tla
      cp -L ${./two_phase_commit_transaction_manager_environment.tla} two_phase_commit_transaction_manager_environment.tla
      cp -L ${./two_phase_commit_transaction_manager_handler_environment.tla} two_phase_commit_transaction_manager_handler_environment.tla
      cp -L ${./two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla} two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla
      cp -L ${./two_phase_commit_transaction_manager_abstract.tla} two_phase_commit_transaction_manager_abstract.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./two_phase_commit_transaction_manager_refined_in_environment_sync.cfg} -workers $WORKERS | tee $out/share/two_phase_commit_transaction_manager_refined_in_environment_sync.log
      '';

  two_phase_commit_transaction_manager_handler_in_environment =
    runCommand
      "two_phase_commit_transaction_manager_handler_in_environment"
      {
        buildInputs = [ tlaplus ];
      }
      ''
      set -euo pipefail

      SPEC=two_phase_commit_transaction_manager_handler_in_environment.tla
      WORKERS=$(( $(nproc) * 3 / 4 ))
      cp -L ${./two_phase_commit_transaction_manager_handler_in_environment.tla} $SPEC
      cp -L ${./two_phase_commit_transaction_manager_handlers.tla} two_phase_commit_transaction_manager_handlers.tla
      cp -L ${./two_phase_commit_transaction_manager_handler_environment.tla} two_phase_commit_transaction_manager_handler_environment.tla
      cp -L ${./two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla} two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./two_phase_commit_transaction_manager_handler_in_environment.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

in
  symlinkJoin
    { name = "all_specs";
      paths =
        [ two_phase_commit_composite
          two_phase_commit_resource_manager_refined_in_environment
          two_phase_commit_transaction_manager_refined_in_environment
          two_phase_commit_transaction_manager_refined_in_environment_sync
          two_phase_commit_transaction_manager_handler_in_environment
        ];
    }
