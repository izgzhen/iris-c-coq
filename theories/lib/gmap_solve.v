Require Import iris.algebra.gmap.

(* Some general tactics for solving map related pure assertions *)

Ltac gmap_solve :=
  lazymatch goal with
  | |- ?H1 ∧ ?H2 => split=>//; gmap_solve
  | |- _ =>
    try (rewrite insert_singleton);
    try (simplify_map_eq);
    eauto
end.
