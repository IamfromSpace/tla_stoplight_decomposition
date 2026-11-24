let
  pkgs = import ./pinned.nix;

  intersection = pkgs.callPackage ./intersection.nix {};

  star_intersection = pkgs.callPackage ./star_intersection/star_intersection.nix {};

  two_phase_commit = pkgs.callPackage ./two_phase_commit/two_phase_commit.nix {};
in
  pkgs.linkFarm "all_projects" [
    { name = "star_intersection"; path = star_intersection; }
    { name = "intersection"; path = intersection; }
    { name = "two_phase_commit"; path = two_phase_commit; }
  ]
