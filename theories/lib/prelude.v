(* Re-export of Iris and some general stuff *)

From iris_c.lib Require Export CpdtTactics Integers.
From iris.prelude Require Export prelude countable strings.
From mathcomp Require Import ssreflect.
Open Scope Z_scope.

Definition ident : Set := string.

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

Close Scope Z_scope.

Lemma leb_trans (x y z: nat):
  (x <=? y) = true →
  (y <=? z) = true →
  (x <=? z) = true.
Proof.
  intros Hxy Hyz.
  apply Nat.leb_le in Hxy. apply Nat.leb_le in Hyz.
  apply Nat.leb_le.
  eapply le_trans; [ apply Hxy | apply Hyz ].
Qed.

Lemma gtb_trans (x y z: nat):
  (x <=? y) = false →
  (y <=? z) = false →
  (x <=? z) = false.
Proof.
  intros Hxy Hyz.
  apply Nat.leb_gt in Hxy.
  apply Nat.leb_gt in Hyz. apply Nat.leb_gt.
  eapply lt_trans; [apply Hyz | apply Hxy ].
Qed.

Lemma leb_cancel_false {A: Type} (c: A) (l1 l2: list A):
  length (c :: l1) + length l2 <=? length l2 = false.
Proof. rewrite Nat.leb_gt. simpl. omega. Qed.

Lemma leb_cancel_true {A: Type} (c: A) (l1 l2: list A):
  length l2 <=? length (c :: l1 ++ l2) = true.
Proof. rewrite Nat.leb_le. simpl. rewrite app_length. omega. Qed.

Ltac destruct_ands :=
  repeat (match goal with
            | [H: context [?H1 ∧ ?H2] |- _ ] => destruct H
          end); subst.

Require Import Coq.Arith.PeanoNat.

Lemma comm_assoc_s x y: x + S y = S x + y. Proof. omega. Qed.
Lemma assoc_s x y: S (x + y) = S x + y. Proof. omega. Qed.
Lemma distri_one x i: x + x * i = x * (i + 1).
Proof.
  rewrite Nat.mul_add_distr_l. rewrite Nat.mul_1_r. omega.
Qed.

Ltac assoc_nat :=
  match goal with
    | |- context [ ?E + (?E1 + ?E2) ] => replace (E + (E1 + E2)) with (E + E1 + E2); [| omega]
    | |- context [ ?E + ?E1 + ?E2 ] => replace (E + E1 + E2) with (E + (E1 + E2)); [| omega]
  end.

Lemma app_cons {A} (x: A) (y: list A):
  [x] ++ y = x::y.
Proof. induction y; crush. Qed.


Ltac rewrite_nat :=
  repeat (match goal with
            | |- context [?X * O] => rewrite Nat.mul_0_r
            | |- context [?X * 1] => rewrite Nat.mul_1_r
            | |- context [?X + O] => rewrite Nat.add_0_r
          end).

Ltac inversion_eq :=
    match goal with
      | [ H1: ?x = ?y1, H2 : ?x = ?y2 |- _ ] => rewrite H1 in H2; inversion H2
      | [ H1: ?x = ?y1, H2 : ?y2 = ?x |- _ ] => rewrite H1 in H2; inversion H2
      | [ H1: ?y1 = ?x, H2 : ?y2 = ?x |- _ ] => rewrite -H1 in H2; inversion H2
      | [ H1: ?y1 = ?x, H2 : ?x = ?y2 |- _ ] => rewrite -H1 in H2; inversion H2
    end.
