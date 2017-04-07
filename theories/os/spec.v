(* Spec Monoid *)

Require Import logic.
From iris.base_logic Require Import soundness gen_heap.
From iris.base_logic Require Export big_op.
From iris.algebra Require Import gmap agree auth frac.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition spec_state := gmap ident val. (* XXX: should be parameterized *)

Definition spec_rel := spec_state → option val → spec_state → Prop.

Inductive spec_code :=
| SCrel (r: spec_rel)
| SCdone (v: option val).

Inductive spec_step : spec_code → spec_state → spec_code → spec_state → Prop :=
| spec_step_rel:
    ∀ (r: spec_rel) s retv s' sf,
      gset_dom sf ⊥ gset_dom s → r s retv s' →
      spec_step (SCrel r) (sf ∪ s) (SCdone retv) (sf ∪ s').

Inductive spec_step_star: spec_code → spec_state → spec_code → spec_state → Prop :=
| SSid: ∀ c s, spec_step_star c s c s
| SStrans:
    ∀ c c' c'' s s' s'',
      spec_step_star c s c' s' → spec_step c' s' c'' s'' → spec_step_star c s c'' s''.

Lemma left_id_ss  (s' : spec_state):
  ∅ ∪ s' = s'.
Admitted.

Lemma spec_step_rel' (r: spec_rel) s retv s':
  r s retv s' → spec_step (SCrel r) s (SCdone retv) s'.
Proof.
  rewrite -{2}(left_id_ss s') -{2}(left_id_ss s).
  intros. apply spec_step_rel=>//.
Qed.

Lemma union_assoc_disj (s1 s2 s: spec_state):
  gset_dom s1 ⊥ gset_dom s2 → s1 ∪ (s2 ∪ s) = (s1 ∪ s2) ∪ s.
Admitted.

Lemma union_disj (sf sf0 s0: spec_state):
  gset_dom sf ⊥ gset_dom (sf0 ∪ s0) → gset_dom sf ⊥ gset_dom sf0.
Admitted.  

Lemma foo (sf0 s0 sf: spec_state):
  gset_dom sf0 ⊥ gset_dom s0 →
  gset_dom sf ⊥ gset_dom (sf0 ∪ s0) →
  gset_dom (sf ∪ sf0) ⊥ gset_dom s0.
Admitted.

Lemma spec_step_framing c c' sf s s':
  gset_dom sf ⊥ gset_dom s → spec_step c s c' s' → spec_step c (sf ∪ s) c' (sf ∪ s').
Proof.
  inversion 2. subst.
  rewrite union_assoc_disj=>//; last by eapply union_disj.
  rewrite union_assoc_disj=>//; last by eapply union_disj.
  by constructor; first by apply foo.
Qed.

(* Naive equivalence *)
Instance spec_code_equiv: Equiv spec_code := (=).

Class specG Σ := SpecG {
  specG_spstG :> gen_heapG ident val Σ;
  specG_specG :> inG Σ (prodR fracR (agreeR (discreteC (spec_code))));
  spec_gname : gname
}.

(* TODO: Missing sub-functors derivation *)

Notation "l S↦ v" :=
  (@mapsto _ _ _ _ _ specG_spstG l 1%Qp v) (at level 20) : uPred_scope.

Section rules.
  Context `{specG Σ}.

  Parameter spec_snapshot: list (spec_state * spec_code) → iProp Σ.
  Parameter spec_master: list (spec_state * spec_code) → iProp Σ.

  Parameter spec_prefix:
    ∀ cs cs',
      spec_master cs ∗ spec_snapshot cs'
      ⊢ ∃ cs'', ⌜ cs = cs'' ++ cs'⌝.

  Parameter spec_snap:
    ∀ cs,
      spec_master cs ⊢ spec_master cs ∗ spec_snapshot cs.

  Parameter spec_grow:
    ∀ c cs, spec_master cs ⊢ spec_master (c::cs).
  
  Definition γ_sstate := @gen_heap_name _ _ _ _ _ specG_spstG.

  Definition sstate (s: spec_state) := ([⋅ map] l ↦ v ∈ s, l S↦ v)%I.
  Definition scode (c: spec_code) := own spec_gname ((1/2)%Qp, (to_agree (c: leibnizC spec_code))).

  Lemma mapsto_singleton l v:
    l S↦ v ⊣⊢ sstate {[ l := v ]}.
  Proof. by rewrite /sstate big_sepM_singleton. Qed.

  Definition spec_inv :=
    (∃ c0 s0 c s cs,
       scode c ∗ own γ_sstate (● to_gen_heap s) ∗
       spec_master ((s, c)::cs) ∗ ⌜ spec_step_star c0 s0 c s ⌝)%I.

  Lemma sstate_update s ss ss':
    own γ_sstate (● to_gen_heap s) ∗
    ([∗ map] l↦v ∈ ss, l S↦ v)
    ⊢ (∃ s', own γ_sstate (● to_gen_heap s') ∗
             ([∗ map] l↦v ∈ ss', l S↦ v) ∗
             ⌜ ∃ sf, gset_dom sf ⊥ gset_dom ss ∧ s = sf ∪ ss ∧ s' = sf ∪ ss' ⌝).
  Proof.
  Admitted.

  Lemma scode_agree ks ks':
   scode ks ∗ scode ks'  ⊢ ⌜ ks = ks' ⌝.
  Proof.
    iIntros "[Hs' Hs]".
    rewrite /scode.
    iDestruct (own_valid_2 with "Hs Hs'") as "%".
    iPureIntro. destruct H0 as [? ?]. simpl in H1.
    by apply to_agree_comp_valid in H1.
  Qed.
  
  Lemma scode_update c1 c2 c3:
    scode c1 ∗ scode c2 ⊢ |==> scode c3 ∗ scode c3 ∗ ⌜ c1 = c2 ⌝.
  Proof.
    iIntros "[Hs Hs']".
    iDestruct (scode_agree with "[-]") as "%"; first iFrame.
    inversion H0. subst.
    rewrite /scode.
    iMod (own_update_2 with "Hs Hs'") as "[Hs Hs']"; last by iFrame.
    rewrite pair_op frac_op' Qp_div_2.
    apply cmra_update_exclusive.
    split; simpl.
    - by rewrite frac_op'.
    - by apply to_agree_comp_valid.
  Qed.
    
  Lemma spec_update ss sc ss' sc':
    spec_step sc ss sc' ss' →
    spec_inv ∗ sstate ss ∗ scode sc
    ⊢ |==> (∃ cs, spec_inv ∗ sstate ss' ∗ scode sc' ∗ spec_snapshot ((ss', sc')::(ss, sc)::cs)).
  Proof.
    (* iIntros (?) "(Hinv & Hss & Hsc)". *)
    (* iDestruct "Hinv" as (c0 s0 c s) "(HSC & HSS & %)". *)
    (* rewrite /sstate /scode. *)
    (* (* HSC Hsc and sc' are easy to prove *) *)
    (* (* ss, s => ss' are hard, might need some framing properties *) *)
    (* iDestruct (sstate_update s ss ss' with "[HSS Hss]") as (s') "(HSS' & Hss' & %)"; first iFrame. *)
    (* iMod (scode_update _ _ sc' with "[HSC Hsc]") as "(HSC' & Hsc' & %)"; first iFrame. *)
    (* iSplitL "HSS' HSC'". *)
    (* { iExists c0, s0, sc', s'. iFrame. *)
    (*   destruct H2 as (sf & ? & ? & ?). *)
    (*   subst. iPureIntro. *)
    (*   eapply SStrans=>//. *)
    (*   apply spec_step_framing=>//. *)
    (* } *)
    (* by iFrame. *)
  Admitted.

  Lemma spec_recover ss sc cs ss0 sc0:
    spec_inv ∗ sstate ss ∗ scode sc ∗ spec_snapshot ((ss0, sc0)::cs)
    ⊢ ⌜ spec_step_star sc0 ss0 sc ss ⌝.
  Admitted.

End rules.

Section sound.
  Context `{specG Σ, clangG Σ} {N: namespace}.

  Inductive simulate: expr → spec_code → Prop :=
  | SimVal: ∀ v, simulate (Evalue v) (SCdone (Some v))
  | SimStep:
      ∀ σ σ' (Σ Σ': spec_state) e c e' c',
        cstep e σ e' σ' →
        spec_step_star c Σ c' Σ →
        simulate e c.

  From iris.program_logic Require Import language adequacy.

  Notation world σ := (wsat ∗ ownE ⊤ ∗ state_interp σ)%I.
  Notation wptp t := ([∗ list] ef ∈ t, WP ef {{ _, True }})%I.


Lemma wp_step R e1 σ1 e2 σ2 efs Φ :
  (R ⊢ |==> ▷ R) →
  prim_step e1 σ1 e2 σ2 efs →
  world σ1 ∗ R ∗ WP e1 {{ Φ }} ==∗ ▷ |==> ◇ (world σ2 ∗ R ∗ WP e2 {{ Φ }} ∗ wptp efs).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (HR Hstep) "[(Hw & HE & Hσ) [HR [H|[_ H]]]]".
  { iDestruct "H" as (v) "[% _]". apply val_stuck in Hstep; simplify_eq. }
  rewrite fupd_eq /fupd_def.
  iMod ("H" $! σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame.
  iModIntro; iNext.
  iMod ("H" $! e2 σ2 efs with "[%] [$Hw $HE]") as ">($ & $ & $ & ? & $)"=>//.
  by iFrame.
Qed.

  Lemma wptp_step' R e1 t1 t2 σ1 σ2 Φ :
    (R ⊢ |==> ▷ R) →
    step (e1 :: t1,σ1) (t2, σ2) →
    world σ1 ∗ R ∗ WP e1 {{ Φ }} ∗ wptp t1
    ==∗ ∃ e2 t2', ⌜t2 = e2 :: t2'⌝ ∗ ▷ |==> ◇ (world σ2 ∗ R ∗ WP e2 {{ Φ }} ∗ wptp t2').
  Proof.
    iIntros (HR Hstep) "(HW & HR & He & Ht)".
    destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
    - iExists e2', (t2' ++ efs); iSplitR; first eauto.
      rewrite big_sepL_app. iFrame "Ht". iApply wp_step; try iFrame; eauto.
    - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto.
      rewrite !big_sepL_app !big_sepL_cons big_sepL_app.
      iDestruct "Ht" as "($ & He' & $)"; iFrame "He".
      iApply wp_step; try iFrame; eauto.
  Qed.
  
  Lemma wptp_steps' R n e1 t1 t2 σ1 σ2 Φ :
    (R ⊢ |==> ▷ R) →
    nsteps (@step clang_lang) n (e1 :: t1, σ1) (t2, σ2) →
    world σ1 ∗ R ∗ WP e1 {{ Φ }} ∗ wptp t1 ⊢
    Nat.iter (S n) (λ P, |==> ▷ P) (∃ e2 t2',
    ⌜t2 = e2 :: t2'⌝ ∗ world σ2 ∗ R ∗ WP e2 {{ Φ }} ∗ wptp t2').
  Proof.
    revert e1 t1 t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 t1 t2 σ1 σ2 /=.
    { intros HR. inversion_clear 1. iIntros "?". eauto 10. }
    iIntros (HR Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']].
    iMod (wptp_step' with "H") as (e1' t1'') "[% H]"; first eauto; simplify_eq. apply H1.
    iModIntro; iNext; iMod "H" as ">?". iApply IH=>//.
    subst. done. Qed.

  Lemma foo' s c:
    (inv N spec_inv ∗ sstate s ∗ scode c) ⊢ |==> ▷ (inv N spec_inv ∗ sstate s ∗ scode c).
  Proof.
    iIntros "?". iModIntro.
    by iNext. Qed.
    
  Lemma soudness n e1 t1 σ1 t2 σ2 Σ1 c1 Σ2 v2:
    nsteps step n (e1 :: t1, σ1) (of_val v2 :: t2, σ2) →
    world σ1 ∗ (inv N spec_inv ∗ sstate Σ1 ∗ scode c1) ∗
    WP e1 {{ v, scode (SCdone (Some v)) ∗ sstate Σ2 }} ∗ wptp t1 ⊢
    Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜simulate (Evalue v2) c1⌝.
  Proof.
    intros. rewrite wptp_steps' //; last by apply foo'.
    rewrite (Nat_iter_S_r (S n)). apply bupd_iter_mono.
    iDestruct 1 as (e2 t2') "(% & (Hw & HE & _) & (?&?&?) & [H _])"; simplify_eq.
    iDestruct (wp_value_inv with "H") as "H". rewrite fupd_eq /fupd_def.
    iMod ("H" with "[Hw HE]") as ">(_ & _ & (?&?))"; first iFrame.
    iModIntro. iNext.
    iDestruct (scode_agree with "[~3 ~1]") as "%"; first iFrame.
    iPureIntro. subst. constructor.
  Qed.

End sound.
