(* Enhanced Integers *)

From iris_c.lib Require Export prelude Integers.
Require Import iris.prelude.prelude.
From mathcomp Require Export ssreflect.

Definition op_safe op (i j: nat) : Prop :=
    Z.to_nat (Byte.intval (op (Byte.repr i) (Byte.repr j))) = i * j.

Definition mul_safe := op_safe Byte.mul.

Coercion Byte.repr : Z >-> int8.

Instance int_eq_dec : EqDecision int.
Proof. apply Int.eq_dec. Defined.
Instance byte_eq_dec : EqDecision byte.
Proof. apply Byte.eq_dec. Defined.
Instance int8_eq_dec : EqDecision int8.
Proof. apply Byte.eq_dec. Defined.
Instance int8_countable : Countable int8.
Admitted.

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
