(* Operational Semantics for the final machine *)

Require Import iris_os.clang.lang.

Definition code : Type := (cureval * context * list context).
