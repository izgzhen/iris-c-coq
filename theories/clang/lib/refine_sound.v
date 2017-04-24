Require Import logic.
From iris.base_logic Require Import soundness gen_heap.
From iris.base_logic Require Export big_op.
From iris.algebra Require Import dra gmap agree auth frac.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.
From iris_c.clang.lib Require Export spec refine.
From iris_c.lib Require Import pair refine_ra.
Set Default Proof Using "Type".
Import uPred.

Section sound.
  Context `{refineG Σ, clangG Σ} {N: namespace}.

  Inductive simulate: expr → spec.spec_code → Prop :=
  | SimVal: ∀ v, simulate (Evalue v) (SCdone (Some v))
  | SimStep:
      ∀ σ σ' (Σ Σ': spec.spec_state) e c e' c' efs,
        cstep e σ e' σ' efs →
        spec_step_star c Σ c' Σ →
        simulate e c.

  Local Hint Constructors simulate.

  From iris.program_logic Require Import language adequacy.

  Notation world σ := (wsat ∗ ownE ⊤ ∗ state_interp σ)%I.
  Notation wptp t := ([∗ list] ef ∈ t, WP ef {{ _, True }})%I.

Lemma wp_step R e1 σ1 e2 σ2 efs Φ :
  (R ⊢ |==> ▷ R) →
  prim_step e1 σ1 e2 σ2 efs →
  world σ1 ∗ R ∗ WP e1 {{ Φ }} ==∗ ▷ |==> ◇ (world σ2 ∗ R ∗ WP e2 {{ Φ }} ∗ wptp efs).
Proof.
  rewrite {1}wp_unfold /wp_pre.
  iIntros (HR Hstep) "[(Hw & HE & Hσ) [HR [H|[_ H]]]]".
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
    iMod (wptp_step' with "H") as (e1' t1'') "[% H]";
      first eauto; simplify_eq. apply H1.
    iModIntro; iNext; iMod "H" as ">?". iApply IH=>//.
    subst. done.
  Qed.

  Lemma bar' ss sc:
    (inv N spec_inv ∗ own_sstate ss ∗ own_scode sc)
    ⊢ |==> ▷ (inv N spec_inv ∗ own_sstate ss ∗ own_scode sc).
  Proof. iIntros "?". iModIntro. by iNext. Qed.

  Lemma soudness n e1 t1 σ1 t2 σ2 c1 Σ1 Σ2 v2:
    nsteps step n (e1 :: t1, σ1) (of_val v2 :: t2, σ2) →
    world σ1 ∗ (inv N spec_inv ∗ own_sstate Σ1 ∗ own_scode c1) ∗
    WP e1 {{ v, own_sstate Σ2 ∗ own_scode (SCdone (Some v)) }} ∗ wptp t1 ⊢
    Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜simulate (Evalue v2) c1⌝.
  Proof.
    intros. rewrite wptp_steps' //; last by apply bar'.
    rewrite (Nat_iter_S_r (S n)). apply bupd_iter_mono.
    iDestruct 1 as (e2 t2') "(% & (Hw & HE & _) & (?&?&?) & [H _])"; simplify_eq.
    iDestruct (wp_value_inv with "H") as "H". rewrite fupd_eq /fupd_def.
    iMod ("H" with "[Hw HE]") as ">(_ & _ & (?&?))"; first iFrame.
    iModIntro. iNext.
    iDestruct (@own_pair_agree spec_state with "[~2 ~1]") as "%"; first iFrame.
    iDestruct (@own_pair_agree spec_code with "[~3 ~4]") as "%"; first iFrame.
    iPureIntro. by simplify_eq.
  Qed.

End sound.
