(** Definition of the physical memory model **)
Require Export lib.Coqlib.
Require Export Integers.
Open Local Scope Z_scope.
Require Import iris.base_logic.base_logic.

Definition block : Set := positive.
Definition offset := nat.
Definition addr : Set := prod block offset.

Instance addr_eq_dec : EqDecision addr.
Proof. solve_decision. Defined.

Inductive byteval : Set :=
| BVundef
| BVint8 (i: int8)
| BVaddr (p: addr) (k: nat)
| BVnull.
