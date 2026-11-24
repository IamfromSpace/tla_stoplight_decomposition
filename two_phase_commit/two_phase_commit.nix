{
  runCommand,
  tlaplus,
  fetchurl,
  symlinkJoin,
}:
let
  tlaplus_examples = "https://raw.githubusercontent.com/tlaplus/Examples/334c3983a2f44ac78fce89d1d20aa79ceb3e6987/specifications/transaction_commit";

  two_phase = fetchurl {
    url = "${tlaplus_examples}/TwoPhase.tla";
    hash = "sha256-5ucu0Al8ylXoC5evM8O8VHkqUEvL32OdbZxmb0nBeBc=";
  };

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
      cp -L ${two_phase} TwoPhase.tla
      cp -L ${t_commit} TCommit.tla
      mkdir -p $out/share
      tlc $SPEC -config ${./two_phase_commit_composite.cfg} -workers $WORKERS | tee $out/share/$SPEC.log
      '';

in
  symlinkJoin
    { name = "all_specs";
      paths =
        [ two_phase_commit_composite
        ];
    }
