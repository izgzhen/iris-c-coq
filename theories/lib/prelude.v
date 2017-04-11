(* Re-export of Iris and some general stuff *)

From iris_os.lib Require Export CpdtTactics Integers.
From iris.prelude Require Import prelude countable.
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

Lemma map_inj {A B} (f: A → B):
  (∀ a1 a2, f a1 = f a2 → a1 = a2) →
  ∀ (l1: list A) l2,
    map f l1 = map f l2 → l1 = l2.
Proof.
  intros Finj.
  induction l1; induction l2.
  - done.
  - intros. simpl in H. inversion H.
  - intros. simpl in H. inversion H.
  - simpl. intros. inversion H.
    apply Finj in H1. apply IHl1 in H2. by subst.
Qed.

Global Instance int32_eq_dec: EqDecision int32 := Int.eq_dec.

Definition int32_encode (i: int32) : positive := encode (Int.unsigned i).
Definition int32_decode (p: positive) : option int32 :=
  match decode p with
    | Some z => Some (Int.repr z)
    | None => None
  end.

Lemma int32_decode_encode i: int32_decode (int32_encode i) = Some i.
Proof. unfold int32_encode, int32_decode. rewrite decode_encode.
       f_equal. apply Int.repr_unsigned.
Qed.

Global Instance int32_countable: Countable int32 :=
  Build_Countable _ _ int32_encode int32_decode int32_decode_encode.
