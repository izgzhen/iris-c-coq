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
    f_sti: ident;
    f_cli: ident;
    f_create_task: ident;
    hpri (γp: name) (i: nat) : iProp Σ;
    closed (γ: name): iProp Σ;
    int_ctx (γ γp: name): iProp Σ;
    (* -- general properties -- *)
    int_ctx_persistent γ γp : PersistentP (int_ctx γ γp);
    closed_timeless γ : TimelessP (closed γ);
    closed_exclusive γ : closed γ -∗ closed γ -∗ False; (* can't close twice *)
    (* HACK *)
    sti : expr := Ecall_typed Tvoid f_sti [];
    cli : expr := Ecall_typed Tvoid f_cli [];
    create_task (f: ident) (p: nat): expr := Ecall_typed Tvoid f_create_task [Eident f; Enat p];
    sti_nj: is_jmp sti = false;
    cli_nj: is_jmp cli = false;
    (* -- operation specs -- *)
    create_task_spec E f e prio Φ :
      text_interp f (Function Tvoid [] e) ∗
      (∀ N: namespace,
         (|={⊤, ⊤∖↑N}=> INVS_range prio ptot) -∗
         (INVS_range prio ptot ={⊤, ⊤∖↑N}=∗ True) -∗
         WP e {{ v, True%I}})
      ⊢ WP create_task f prio @ E {{ Φ }};
    sti_spec prio γ γp Φ :
      int_ctx γ γp ∗ hpri γp prio ∗ INVS_up prio ∗ closed γ ∗ (hpri γp prio -∗ Φ Vvoid)
      ⊢ WP sti {{ Φ }};
    cli_spec prio γ γp Φ :
      int_ctx γ γp ∗ hpri γp prio ∗ (INVS_up prio -∗ hpri γp prio -∗ closed γ -∗ Φ Vvoid)
      ⊢ WP cli {{ Φ }}
  }.
End definitions.

Existing Instances int_ctx_persistent closed_timeless.

Arguments interrupt {_ _} _ _.
Arguments hpri {_ _} _ {_ _} _ _.
Arguments closed {_ _} _ {_ _} _.
Arguments int_ctx {_ _} _ {_} _ _ _.
