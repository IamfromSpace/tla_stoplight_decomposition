{ rustPlatform, lib }:
  let fs = lib.fileset;

  in rustPlatform.buildRustPackage {
    pname = "two-phase-commit-rust";
    version = "0.0.1";

    cargoLock = {
      lockFile = ./Cargo.lock;
    };
    src =
      fs.toSource {
        root = ./.;
        fileset =
          fs.unions [
            ./Cargo.toml
            ./Cargo.lock
            (fs.fileFilter (x: x.hasExt "rs") ./src)
          ];
      };
  }
