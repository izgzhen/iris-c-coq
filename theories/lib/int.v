(* Enhanced Integers *)

From iris_c.lib Require Export prelude Integers.
Require Import iris.prelude.prelude.
From mathcomp Require Export ssreflect.

Definition op_safe op opn (i j: nat) : Prop :=
    Z.to_nat (Byte.intval (op (Byte.repr i) (Byte.repr j))) = opn i j.

Definition mul_safe := op_safe Byte.mul Init.Nat.mul.

Coercion Byte.repr : Z >-> int8.

Global Instance int_eq_dec : EqDecision int.
Proof. apply Int.eq_dec. Defined.
Global Instance byte_eq_dec : EqDecision byte.
Proof. apply Byte.eq_dec. Defined.
Global Instance int8_eq_dec : EqDecision int8.
Proof. apply Byte.eq_dec. Defined.
Global Instance int32_eq_dec: EqDecision int32 := Int.eq_dec.

Definition int8_encode (i: int8) : positive := encode (Byte.unsigned i).
Definition int8_decode (p: positive) : option int8 :=
  match decode p with
    | Some z => Some (Byte.repr z)
    | None => None
  end.

Lemma int8_decode_encode i: int8_decode (int8_encode i) = Some i.
Proof. unfold int8_encode, int8_decode. rewrite decode_encode.
       f_equal. apply Byte.repr_unsigned. Qed.

Global Instance int8_countable: Countable int8 :=
  Build_Countable _ _ int8_encode int8_decode int8_decode_encode.

Bind Scope int_scope with int.
Delimit Scope int_scope with int.

Notation "i1 + i2" := (Byte.add i1%int i2%int)
  (at level 50, left associativity) : int_scope.
Notation "i1 * i2" := (Byte.mul i1%int i2%int)
  (at level 40, left associativity) : int_scope.
Notation "i1 - i2" := (Byte.sub i1%int i2%int)
  (at level 50, left associativity) : int_scope.

Ltac rewrite_byte :=
  match goal with
    | |- context [ Byte.mul _ (Byte.repr Z0) ] => rewrite Byte.mul_zero
    | |- context [ offset_by_byte ?off Byte.zero ] =>
      rewrite /offset_by_byte;
        replace (Z.to_nat (Byte.intval Byte.zero)) with O; last done;
        replace (off + O) with off; last done
    | |- context [ offset_by_byte ?off (Byte.repr ?b) ] =>
      rewrite /offset_by_byte;
        replace (Z.to_nat (Byte.intval (Byte.repr b))) with (Z.to_nat b); last done
  end.
