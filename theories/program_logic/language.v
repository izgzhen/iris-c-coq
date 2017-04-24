From iris.algebra Require Export ofe.
Set Default Proof Using "Type".

Structure language := Language {
  expr : Type;
  val : Type;
  local_state : Type;
  state : Type;
  of_val : val → expr;
  to_val : expr → option val;
  init_local: local_state;
  prim_step : expr → local_state → state → expr → local_state → state → list expr → Prop;
  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e l σ e' l' σ' efs : prim_step e l σ e' l' σ' efs → to_val e = None
}.
Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Bind Scope val_scope with val.
Arguments of_val {_} _.
Arguments to_val {_} _.
Arguments prim_step {_} _ _ _ _ _ _ _.
Arguments to_of_val {_} _.
Arguments of_to_val {_} _ _ _.
Arguments val_stuck {_} _ _ _ _ _ _ _ _.

Canonical Structure stateC Λ := leibnizC (state Λ).
Canonical Structure local_stateC Λ := leibnizC (local_state Λ).
Canonical Structure valC Λ := leibnizC (val Λ).
Canonical Structure exprC Λ := leibnizC (expr Λ).

Definition cfg (Λ : language) := (list (expr Λ * local_state Λ) * state Λ)%type.

Section language.
  Context {Λ : language}.
  Implicit Types v : val Λ.

  Definition reducible (e : expr Λ) (l: local_state Λ) (σ : state Λ) :=
    ∃ e' l' σ' efs, prim_step e l σ e' l' σ' efs.
  Definition irreducible (e : expr Λ) (l: local_state Λ) (σ : state Λ) :=
    ∀ e' l' σ' efs, ¬prim_step e l σ e' l' σ' efs.
  Definition atomic (e : expr Λ) : Prop :=
    ∀ l σ e' l' σ' efs, prim_step e l σ e' l' σ' efs → irreducible e' l' σ'.
  Inductive step (ρ1 ρ2 : cfg Λ) : Prop :=
    | step_atomic e1 l1 σ1 e2 l2 σ2 efs t1 t2 :
       ρ1 = (t1 ++ (e1, l1) :: t2, σ1) →
       ρ2 = (t1 ++ (e2, l2) :: t2 ++ map (,init_local Λ) efs, σ2) →
       prim_step e1 l1 σ1 e2 l2 σ2 efs →
       step ρ1 ρ2.

  Lemma of_to_val_flip v e : of_val v = e → to_val e = Some v.
  Proof. intros <-. by rewrite to_of_val. Qed.
  Lemma reducible_not_val e l σ : reducible e l σ → to_val e = None.
  Proof. intros (?&?&?&?&?); eauto using val_stuck. Qed.
  Lemma val_irreducible e l σ : is_Some (to_val e) → irreducible e l σ.
  Proof. intros [??] ???? ?%val_stuck. by destruct (to_val e). Qed.
  Global Instance of_val_inj : Inj (=) (=) (@of_val Λ).
  Proof. by intros v v' Hv; apply (inj Some); rewrite -!to_of_val Hv. Qed.
End language.
