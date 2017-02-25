(* Interrupt Mechanism *)

Require Import logic.

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
    hpri (γp: name) (i: nat) : iProp Σ;
    closed (γ: name): iProp Σ;
    int_ctx (N: namespace) (γ γp: name): iProp Σ;
    (* -- general properties -- *)
    (* int_ctx_ne N γ γp n: Proper (dist n ==> dist n) (int_ctx N γ γp); *) (* FIXME *)
    int_ctx_persistent N γ γp : PersistentP (int_ctx N γ γp);
    closed_timeless γ : TimelessP (closed γ);
    closed_exclusive γ : closed γ -∗ closed γ -∗ False;
    (* -- operation specs -- *)
    sti_spec N prio γ γp Φ Φret :
      int_ctx N γ γp ∗ hpri γp prio ∗ INVS_up prio ∗ closed γ ∗ (hpri γp prio -∗ Φ)
      ⊢ WP curs (Sprim Psti) {{ _, Φ; Φret }};
    cli_spec N prio γ γp Φ Φret :
      int_ctx N γ γp ∗ hpri γp prio ∗ (INVS_up prio -∗ hpri γp prio -∗ closed γ -∗ Φ)
      ⊢ WP curs (Sprim Pcli) {{ _, Φ; Φret }}
  }.
End definitions.

Existing Instances int_ctx_persistent closed_timeless.

Arguments interrupt {_ _} _.
Arguments hpri {_ _} _ {_} _ _.
Arguments closed {_ _} _ {_} _.
Arguments int_ctx {_ _} _ {_} _ _ _.
