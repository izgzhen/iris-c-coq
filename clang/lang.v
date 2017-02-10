From iris.program_logic Require Export ectx_language ectxi_language.
From iris.prelude Require Import gmap.
From iris_os.clang Require Import Integers.
Set Default Proof Using "Type".

Open Scope Z_scope.

(* Memory *)
Definition block_id := positive.
Definition offset := Z.
Definition addr : Set := block_id * offset.

Inductive memval :=
| Undef: memval
| Byte: byte → memval
| Pointer: block_id → int32 → nat → memval
| MNull: memval.
               
Definition ident := Z.





