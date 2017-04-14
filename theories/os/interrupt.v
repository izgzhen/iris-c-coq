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
      | O => invs O
    end.

(* Definition interrupt_handler_pre (γie γpri: gname) (prio: nat) := *)
(*   (own γie (Excl ()) ∗ hpri γpri prio ∗ INVS prio)%I. *)

  Definition INVS_up (p: nat) :=
    match p with
      | O => True%I
      | S p' => INVS p'
    end.

  (* Interface *)

  Structure interrupt := Interrupt {
    (* -- predicates -- *)
    name : Type;
    f_sti: ident;
    f_cli: ident;
    hpri (γp: name) (i: nat) : iProp Σ;
    closed (γ: name): iProp Σ;
    int_ctx (N: namespace) (γ γp: name): iProp Σ;
    (* -- general properties -- *)
    (* int_ctx_ne N γ γp n: Proper (dist n ==> dist n) (int_ctx N γ γp); *) (* FIXME *)
    int_ctx_persistent N γ γp : PersistentP (int_ctx N γ γp);
    closed_timeless γ : TimelessP (closed γ);
    closed_exclusive γ : closed γ -∗ closed γ -∗ False;
    (* HACK *)
    sti : expr := Ecall f_sti [];
    cli : expr := Ecall f_cli [];
    sti_nj: is_jmp sti = false;
    cli_nj: is_jmp cli = false;
    (* -- operation specs -- *)
    sti_spec N prio γ γp Φ :
      int_ctx N γ γp ∗ hpri γp prio ∗ INVS_up prio ∗ closed γ ∗ (hpri γp prio -∗ Φ Vvoid)
      ⊢ WP sti {{ Φ }};
    cli_spec N prio γ γp Φ :
      int_ctx N γ γp ∗ hpri γp prio ∗ (INVS_up prio -∗ hpri γp prio -∗ closed γ -∗ Φ Vvoid)
      ⊢ WP cli {{ Φ }}
  }.
End definitions.

Existing Instances int_ctx_persistent closed_timeless.

Arguments interrupt {_ _} _.
Arguments hpri {_ _} _ {_} _ _.
Arguments closed {_ _} _ {_} _.
Arguments int_ctx {_ _} _ {_} _ _ _.
