(* Interrupt Mechanism *)
(* Spec Monoid *)

Require Import logic.
From iris.base_logic Require Export big_op.
From iris.algebra Require Import agree auth.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.
Require Import iris_os.clang.lib.Integers.
Set Default Proof Using "Type".
Import uPred.


(* TODO: implementation *)
(* Class intG (n: nat) Σ := IntG { *)
(*   intG_ieG :> inG Σ (exclR unitC); (* FIXME: un-reentrant lock *) *)
(*   intG_hpriG :> inG Σ (authR (optionUR (agreeR (leibnizC nat)))) (* highest priority *) *)
(* }. *)

Section definitions.
  Context `{!clangG Σ} {invs: nat → iProp Σ}.

  Fixpoint INVS (p: nat) :=
    match p with
      | S p' => (invs p ∗ INVS p')%I
      | 0 => invs 0
    end.

(* Definition interrupt_handler_pre (γie γpri: gname) (prio: nat) := *)
(*   (own γie (Excl ()) ∗ hpri γpri prio ∗ INVS prio)%I. *)

  Definition INVS_up (p: nat) :=
    match p with
      | 0 => True%I
      | S p' => INVS p'
    end.

  (* Interface *)
  
  Structure interrupt := Interrupt {
    (* -- predicates -- *)
    name : Type;
    hpri (γ: name) (i: nat) : iProp Σ;
    closed (γ: name): iProp Σ;
    (* -- TODO: general properties -- *)
    closed_timeless γ : TimelessP (closed γ);
    closed_exclusive γ : closed γ -∗ closed γ -∗ False;
    (* -- operation specs -- *)
    sti_spec prio γ Φ Φret :
      INVS_up prio ∗ closed γ ∗ (True -∗ Φ)
      ⊢ WP (curs (Sprim Psti), knil) {{ _, Φ; Φret }};
    cli_spec prio γ Φ Φret :
      (INVS_up prio -∗ closed γ -∗ Φ)
      ⊢ WP (curs (Sprim Pcli), knil) {{ _, Φ; Φret }}
  }.
End definitions.
