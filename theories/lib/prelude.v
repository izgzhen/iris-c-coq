(* Re-export of Iris and some general stuff *)

From iris_os.lib Require Export CpdtTactics Integers.
Require Import iris.prelude.prelude.
Open Scope Z_scope.

Definition ident : Set := Z.

Lemma drop_app {A} (xs ys: list A):
  drop (length xs) (xs ++ ys) = ys.
Proof. generalize ys. induction xs; crush. Qed.

Lemma take_drop_app {A} (xs ys: list A) n:
  length xs ≥ n → drop n (take n xs ++ ys) = ys.
Proof.
  intros ?. replace n with (length (take n xs)) at 1.
  - apply drop_app.
  - apply take_length_le. done.
Qed.
