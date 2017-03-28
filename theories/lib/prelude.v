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

Definition is_some {A} (x: option A): bool := match x with Some _ => true | None => false end.

Definition offset_by_int32 (o: nat) (i: int32) : nat := o + Z.to_nat (Int.intval i).
Definition offset_by_byte (o: nat) (i: byte) : nat := o + Z.to_nat (Byte.intval i).

Fixpoint lift_list_option {A} (l: list (option A)): option (list A) :=
  match l with
    | Some x :: l' => (x ::) <$> lift_list_option l'
    | None :: _ => None
    | _ => Some []
  end.
