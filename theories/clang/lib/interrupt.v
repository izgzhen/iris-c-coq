(* Interrupt Mechanism *)

Require Import logic.

Section definitions.
  Context `{!clangG Σ} {invs: nat → iProp Σ} {ptot: nat}.

  Fixpoint INVS (p: nat) :=
    match p with
      | S p' => (invs p ∗ INVS p')%I
      | O => invs O
    end.

  Definition INVS_up (p: nat) :=
    match p with
      | O => True%I
      | S p' => INVS p'
    end.

  Fixpoint INVS_range (p: nat) (q: nat) : iProp Σ :=
    if bool_decide (p > q) then True%I
    else match q with
           | O => invs O
           | S q' => (invs q ∗ INVS_range p q')%I
         end.

  (* Interface *)

  Structure interrupt := Interrupt {
    (* -- predicates -- *)
    name : Type;
    f_sti: val;
    f_cli: val;
    f_create_task (f: ident) (p: nat) : val;
    hpri (γp: name) (i: nat) : iProp Σ;
    closed (γ: name): iProp Σ;
    int_ctx (γ γp: name): iProp Σ;
    (* -- general properties -- *)
    int_ctx_persistent γ γp : PersistentP (int_ctx γ γp);
    closed_timeless γ : TimelessP (closed γ);
    closed_exclusive γ : closed γ -∗ closed γ -∗ False; (* can't close twice *)
    (* HACK *)
    sti : expr := Evalue f_sti;
    cli : expr := Evalue f_cli;
    create_task f p : expr := Evalue $ f_create_task f p;
    (* -- operation specs -- *)
    create_task_spec E f e prio Φ ks:
      f T↦ Function Tvoid [] e ∗
      (∀ N: namespace,
         ⌜ ∀ E, N ⊥ E ⌝ -∗ INVS_range prio ptot -∗
         WP (e, ([], semp)) @ ⊤∖↑N {{ v, INVS_range prio ptot}})
      ⊢ WP (create_task f prio, ks) @ E {{ Φ }};
    sti_spec prio γ γp Φ ks:
      int_ctx γ γp ∗ hpri γp prio ∗ INVS_up prio ∗ closed γ ∗ (hpri γp prio -∗ Φ Vvoid)
      ⊢ WP (sti, ks) {{ Φ }};
    cli_spec prio γ γp Φ ks:
      int_ctx γ γp ∗ hpri γp prio ∗ (INVS_up prio -∗ hpri γp prio -∗ closed γ -∗ Φ Vvoid)
      ⊢ WP (cli, ks) {{ Φ }}
  }.
End definitions.

Existing Instances int_ctx_persistent closed_timeless.

Arguments interrupt {_ _} _ _.
Arguments hpri {_ _} _ {_ _} _ _.
Arguments closed {_ _} _ {_ _} _.
Arguments int_ctx {_ _} _ {_} _ _ _.
