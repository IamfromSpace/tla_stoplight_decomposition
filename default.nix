let
  pkgs = import ./pinned.nix;

  intersection = pkgs.callPackage ./intersection.nix {};

  star_intersection = pkgs.callPackage ./star_intersection/star_intersection.nix {};
in
  pkgs.linkFarm "all_projects" [
    { name = "star_intersection"; path = star_intersection; }
    { name = "intersection"; path = intersection; }
  ]
