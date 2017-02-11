From iris.program_logic Require Export ectx_language ectxi_language.
From iris.prelude Require Import gmap.
From iris_os.clang Require Import Integers.
Set Default Proof Using "Type".

Open Scope Z_scope.

(* Memory *)
Definition block_id := positive.
Definition offset := Z.
Definition addr : Set := block_id * offset.
Definition addrval : Set := block_id * int32.

Inductive memval :=
| Undef: memval
| Byte: byte → memval
| Pointer: block_id → int32 → nat → memval
| MNull: memval.

Definition mem := gmap addr memval.

Inductive val :=
| Vundef
| Vnull
| Vint32: int → val
| Vptr: addrval → val.

Definition ident := Z.

Inductive type :=
| Tnull | Tvoid | Tint8 | Tint16 | Tint32
| Tptr: type → type
| Tcom_ptr: ident → type
| Tarray: type → nat → type
| Tstruct: ident → list (ident * type) → type.

Definition decllist := list (ident * type).

Inductive uop :=
 | oppsite
 | negation.

Inductive bop :=
 | oplus | ominus | omulti | odiv | olshift | orshift
 | oand | oor | obitand | obitor | oeq | olt.

Definition env := gmap ident (block_id * type).

(* Language *)

(** Expression **)
Inductive expr:=
 | enull : expr
 | evar : ident -> expr
 | econst32 : int32 -> expr
 | eunop : uop -> expr -> expr
 | ebinop : bop -> expr -> expr -> expr
 | ederef : expr -> expr
 | eaddrof : expr -> expr 
 | efield : expr -> ident -> expr
 | ecast : expr -> type -> expr
 | earrayelem : expr -> expr -> expr.  (* expr1 [ expr2 ] *)

Inductive stmts :=
 | sskip : option val -> stmts
 | sassign : expr -> expr -> stmts (* expr1 = expr2 *)
 | sif : expr -> stmts -> stmts -> stmts (* if ( expr ) stmts1 else stmts2 *)
 | sifthen : expr -> stmts -> stmts
 | swhile : expr -> stmts -> stmts
 | sret : stmts
 | srete : expr -> stmts
 | scall : ident -> list expr -> stmts
 | scalle : expr -> ident -> list expr -> stmts
 | sseq : stmts -> stmts -> stmts (* right associative *)
 | sprint : expr -> stmts
 | sfexec : ident -> list val -> list type -> stmts
 | sfree : list (block_id * type) -> option val -> stmts
 | salloc : list val -> decllist -> stmts.


Inductive exprcont:=
| kenil : exprcont
| keop1 : uop -> type -> exprcont -> exprcont
| keop2r : bop -> expr -> type -> type -> exprcont -> exprcont
| keop2l: bop -> val -> type -> type ->exprcont -> exprcont
| kederef : type -> exprcont -> exprcont 
| keoffset: int32 -> exprcont -> exprcont
| kearrbase: expr -> type -> exprcont -> exprcont
| kearrindex: val -> type -> exprcont -> exprcont
| kecast: type -> type -> exprcont -> exprcont.

Inductive stmtcont:=
| kstop : stmtcont
| kseq : stmts -> stmtcont -> stmtcont
| kcall : ident -> stmts -> env -> stmtcont -> stmtcont
| kassignr: expr -> type -> stmtcont -> stmtcont
| kassignl : val -> type -> stmtcont -> stmtcont
| kfuneval : ident -> list val -> list type -> list expr -> stmtcont -> stmtcont
| kif : stmts -> stmts -> stmtcont -> stmtcont
| kwhile : expr -> stmts -> stmtcont -> stmtcont
| kret : stmtcont -> stmtcont.

Inductive cureval:=
|cure : expr -> cureval
|curs : stmts -> cureval.


