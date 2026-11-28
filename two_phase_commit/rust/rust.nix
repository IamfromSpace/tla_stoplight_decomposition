{ rustPlatform, lib, tlaplus }:
  let fs = lib.fileset;

  in rustPlatform.buildRustPackage {
    pname = "two-phase-commit-rust";
    version = "0.0.1";

    cargoLock = {
      lockFile = ./Cargo.lock;
    };
    cargoRoot = "rust";
    buildAndTestSubdir = "rust";
    nativeCheckInputs = [ tlaplus ];
    src =
      fs.toSource {
        root = ../.;
        fileset =
          fs.unions [
            ./Cargo.toml
            ./Cargo.lock
            (fs.fileFilter (x: x.hasExt "rs") ./src)
            ../two_phase_commit_transaction_manager_handler_trace.tla
            ../two_phase_commit_transaction_manager_handler_in_environment.tla
            ../two_phase_commit_transaction_manager_handlers.tla
            ../two_phase_commit_transaction_manager_handler_environment.tla
            ../two_phase_commit_transaction_manager_handler_environment_sync_adapter.tla
          ];
      };
  }
