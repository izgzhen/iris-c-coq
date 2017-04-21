(* Enhanced Integers *)

Require Export iris_c.lib.Integers.
Require Import iris.prelude.prelude.

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
