(* Enhanced Integers *)

From iris_c.lib Require Export prelude Integers.
Require Import iris.prelude.prelude.
From mathcomp Require Export ssreflect.

Definition op_safe op (i j: nat) : Prop :=
    Z.to_nat (Int.intval (op (Int.repr i) (Int.repr j))) = i * j.

Definition mul_safe := op_safe Int.mul.

Coercion Int.repr : Z >-> int32.

Bind Scope int_scope with int.
Delimit Scope int_scope with int.

Notation "i1 + i2" := (Int.add i1%int i2%int)
  (at level 50, left associativity) : int_scope.
Notation "i1 * i2" := (Int.mul i1%int i2%int)
  (at level 40, left associativity) : int_scope.
Notation "i1 - i2" := (Int.sub i1%int i2%int)
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

Ltac rewrite_int :=
  match goal with
    | |- context [ Int.mul _ (Int.repr Z0) ] => rewrite Int.mul_zero
    | |- context [ offset_by_int32 ?off Int.zero ] =>
      rewrite /offset_by_int32;
        replace (Z.to_nat (Int.intval Int.zero)) with O; last done;
        replace (off + O) with off; last done
    | |- context [ offset_by_int32 ?off (Int.repr ?b) ] =>
      rewrite /offset_by_int32;
        replace (Z.to_nat (Int.intval (Int.repr b))) with (Z.to_nat b); last done
  end.
