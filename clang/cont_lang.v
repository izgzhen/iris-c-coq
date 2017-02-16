(** An axiomatization of evaluation-context based languages, including a proof
    that this gives rise to a "language" in the Iris sense. *)
From iris.algebra Require Export base.
From iris.program_logic Require Import language.
Set Default Proof Using "Type".
From iris.prelude Require Export strings.

(* We need to make thos arguments indices that we want canonical structure
   inference to use a keys. *)
Class ContLanguage (expr val ectx state fundecls cont : Type) := {
  of_val : val → expr;
  to_val : expr → option val;
  empty_ectx : ectx;
  comp_ectx : ectx → ectx → ectx;
  fill : ectx → expr → expr;
  head_step : expr → state → expr → state → list expr → Prop;
  cont_step : fundecls → expr → ectx → cont → expr → cont → Prop;

  to_of_val v : to_val (of_val v) = Some v;
  of_to_val e v : to_val e = Some v → of_val v = e;
  val_stuck e1 σ1 e2 σ2 efs : head_step e1 σ1 e2 σ2 efs → to_val e1 = None;

  fill_empty e : fill empty_ectx e = e;
  fill_comp K1 K2 e : fill K1 (fill K2 e) = fill (comp_ectx K1 K2) e;
  fill_inj K :> Inj (=) (=) (fill K);
  fill_not_val K e : to_val e = None → to_val (fill K e) = None;

  (* There are a whole lot of sensible axioms (like associativity, and left and
  right identity, we could demand for [comp_ectx] and [empty_ectx]. However,
  positivity suffices. *)
  ectx_positive K1 K2 :
    comp_ectx K1 K2 = empty_ectx → K1 = empty_ectx ∧ K2 = empty_ectx;

  step_by_val K K' e1 e1' σ1 e2 σ2 efs :
    fill K e1 = fill K' e1' →
    to_val e1 = None →
    head_step e1' σ1 e2 σ2 efs →
    exists K'', K' = comp_ectx K K'';
}.

Arguments of_val {_ _ _ _ _ _ _} _.
Arguments to_val {_ _ _ _ _ _ _} _.
Arguments empty_ectx {_ _ _ _ _ _ _}.
Arguments comp_ectx {_ _ _ _ _ _ _} _ _.
Arguments fill {_ _ _ _ _ _ _} _ _.
Arguments head_step {_ _ _ _ _ _ _} _ _ _ _ _.

Arguments to_of_val {_ _ _ _ _ _ _} _.
Arguments of_to_val {_ _ _ _ _ _ _} _ _ _.
Arguments val_stuck {_ _ _ _ _ _ _} _ _ _ _ _ _.
Arguments fill_empty {_ _ _ _ _ _ _} _.
Arguments fill_comp {_ _ _ _ _ _ _} _ _ _.
Arguments fill_not_val {_ _ _ _ _ _ _} _ _ _.
Arguments ectx_positive {_ _ _ _ _ _ _} _ _ _.
Arguments step_by_val {_ _ _ _ _ _ _} _ _ _ _ _ _ _ _ _ _ _.

(* From an ectx_language, we can construct a language. *)
Section ectx_language.
  Context {expr val ectx state fundecls cont} {Λ : ContLanguage expr val ectx state fundecls cont}.
  Implicit Types (e : expr) (K : ectx).

  Definition head_reducible (e : expr) (σ : state) :=
    ∃ e' σ' efs, head_step e σ e' σ' efs.

  Inductive prim_step (e1 : expr) (σ1 : state)
      (e2 : expr) (σ2 : state) (efs : list expr) : Prop :=
    Cont_step K e1' e2' :
      e1 = fill K e1' → e2 = fill K e2' →
      head_step e1' σ1 e2' σ2 efs → prim_step e1 σ1 e2 σ2 efs.

  Lemma Cont_step' K e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs → prim_step (fill K e1) σ1 (fill K e2) σ2 efs.
  Proof. econstructor; eauto. Qed.

  Lemma val_prim_stuck e1 σ1 e2 σ2 efs :
    prim_step e1 σ1 e2 σ2 efs → to_val e1 = None.
  Proof. intros [??? -> -> ?]; eauto using fill_not_val, val_stuck. Qed.

  Canonical Structure ectx_lang : language := {|
    language.expr := expr; language.val := val; language.state := state;
    language.of_val := of_val; language.to_val := to_val;
    language.prim_step := prim_step;
    language.to_of_val := to_of_val; language.of_to_val := of_to_val;
    language.val_stuck := val_prim_stuck;
  |}.

  (* Some lemmas about this language *)
  Lemma head_prim_step e1 σ1 e2 σ2 efs :
    head_step e1 σ1 e2 σ2 efs → prim_step e1 σ1 e2 σ2 efs.
  Proof. apply Cont_step with empty_ectx; by rewrite ?fill_empty. Qed.

  Lemma head_prim_reducible e σ : head_reducible e σ → reducible e σ.
  Proof. intros (e'&σ'&efs&?). eexists e', σ', efs. by apply head_prim_step. Qed.

  Lemma ectx_language_atomic e :
    (∀ σ e' σ' efs, head_step e σ e' σ' efs → irreducible e' σ') →
    (∀ K e', e = fill K e' → to_val e' = None → K = empty_ectx) →
    atomic e.
  Proof.
    intros Hatomic_step Hatomic_fill σ e' σ' efs [K e1' e2' -> -> Hstep].
    assert (K = empty_ectx) as -> by eauto 10 using val_stuck.
    rewrite fill_empty. eapply Hatomic_step. by rewrite fill_empty.
  Qed.

  Lemma head_reducible_prim_step e1 σ1 e2 σ2 efs :
    head_reducible e1 σ1 → prim_step e1 σ1 e2 σ2 efs →
    head_step e1 σ1 e2 σ2 efs.
  Proof.
    intros (e2''&σ2''&efs''&?) [K e1' e2' -> -> Hstep].
    destruct (step_by_val K empty_ectx e1' (fill K e1') σ1 e2'' σ2'' efs'')
      as [K' [-> _]%symmetry%ectx_positive];
      eauto using fill_empty, fill_not_val, val_stuck.
    by rewrite !fill_empty.
  Qed.

  (* Every evaluation context is a context. *)
  Global Instance ectx_lang_ctx K : LanguageCtx ectx_lang (fill K).
  Proof.
    split.
    - eauto using fill_not_val.
    - intros ????? [K' e1' e2' Heq1 Heq2 Hstep].
      by exists (comp_ectx K K') e1' e2'; rewrite ?Heq1 ?Heq2 ?fill_comp.
    - intros e1 σ1 e2 σ2 ? Hnval [K'' e1'' e2'' Heq1 -> Hstep].
      destruct (step_by_val K K'' e1 e1'' σ1 e2'' σ2 efs) as [K' ->]; eauto.
      rewrite -fill_comp in Heq1; apply (inj (fill _)) in Heq1.
      exists (fill K' e2''); rewrite -fill_comp; split; auto.
      econstructor; eauto.
  Qed.
End ectx_language.

Arguments ectx_lang _ {_ _ _ _ _ _}.
