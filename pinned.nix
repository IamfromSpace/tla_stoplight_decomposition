import
  (builtins.fetchTarball {
    name = "nixos-26.05";
    url = "https://releases.nixos.org/nixos/26.05/nixos-26.05.15079.0dc498bfe49b/nixexprs.tar.xz";
    sha256 = "sha256:11bidflcplzwprk6wzpgg1ypx3qsb990l8mybcrmg1ggypmmjf25";
  })
  {}
