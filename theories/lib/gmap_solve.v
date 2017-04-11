Require Import iris.algebra.gmap.

(* Some general tactics for solving map related pure assertions *)

Ltac gmap_rewrite :=
  (rewrite insert_singleton)
    || (rewrite insert_empty)
    || (rewrite lookup_singleton)
    || (rewrite map_to_list_singleton)
    || simpl.

Ltac gmap_simplify :=
  lazymatch goal with
  | |- ?H1 ∧ ?H2 => split=>//; gmap_simplify
  | |- _ => simplify_map_eq; try gmap_rewrite
end.
