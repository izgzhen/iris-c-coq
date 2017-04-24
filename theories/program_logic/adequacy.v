From iris_c.program_logic Require Export weakestpre.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op soundness.
From iris.base_logic.lib Require Import wsat.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

(* Global functor setup *)
Definition invΣ : gFunctors :=
  #[GFunctor (authRF (gmapURF positive (agreeRF (laterCF idCF))));
    GFunctor coPset_disjUR;
    GFunctor (gset_disjUR positive)].

Class invPreG (Σ : gFunctors) : Set := WsatPreG {
  inv_inPreG :> inG Σ (authR (gmapUR positive (agreeR (laterC (iPreProp Σ)))));
  enabled_inPreG :> inG Σ coPset_disjR;
  disabled_inPreG :> inG Σ (gset_disjR positive);
}.

Instance subG_invΣ {Σ} : subG invΣ Σ → invPreG Σ.
Proof. solve_inG. Qed.

(* Allocation *)
Lemma wsat_alloc `{invPreG Σ} : (|==> ∃ _ : invG Σ, wsat ∗ ownE ⊤)%I.
Proof.
  iIntros.
  iMod (own_alloc (● (∅ : gmap _ _))) as (γI) "HI"; first done.
  iMod (own_alloc (CoPset ⊤)) as (γE) "HE"; first done.
  iMod (own_alloc (GSet ∅)) as (γD) "HD"; first done.
  iModIntro; iExists (WsatG _ _ _ _ γI γE γD).
  rewrite /wsat /ownE; iFrame.
  iExists ∅. rewrite fmap_empty big_sepM_empty. by iFrame.
Qed.

(* Program logic adequacy *)
Record adequate {Λ} (e1 : expr Λ) (l1: local_state Λ) (σ1 : state Λ) (φ : val Λ → Prop) := {
  adequate_result t2 l2 σ2 v2 :
   rtc step ([(e1, l1)], σ1) ((of_val v2, l2) :: t2, σ2) → φ v2;
  adequate_safe t2 σ2 e2 l2 :
   rtc step ([(e1, l1)], σ1) (t2, σ2) →
   (e2, l2) ∈ t2 → (is_Some (to_val e2) ∨ reducible e2 l2 σ2)
}.

Theorem adequate_tp_safe {Λ} (e1 : expr Λ) l1 t2 σ1 σ2 φ :
  adequate e1 l1 σ1 φ →
  rtc step ([(e1, l1)], σ1) (t2, σ2) →
  Forall (λ e, is_Some (to_val (e.1))) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3).
Proof.
  intros Had ?.
  destruct (decide (Forall (λ e, is_Some (to_val (e.1))) t2)) as [|Ht2]; [by left|].
  apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as ((e2&l2)&?&He2).
  destruct (adequate_safe e1 l1 σ1 φ Had t2 σ2 e2 l2) as [?|(e3&l3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. eauto. }
  destruct (elem_of_list_split t2 (e2, l2)) as (t2'&t2''&->); auto.
  right; exists (t2' ++ (e3, l3) :: t2'' ++ (map (,init_local Λ) efs)), σ3; econstructor; eauto.
Qed.

Section adequacy.
Context `{irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation world σ := (wsat ∗ ownE ⊤ ∗ state_interp σ)%I.

Notation wptp t := ([∗ list] ef ∈ t, WP (ef.1) {{ _, True }})%I.

Lemma wp_step e1 l1 σ1 e2 l2 σ2 efs Φ :
  prim_step e1 l1 σ1 e2 l2 σ2 efs →
  world σ1 ∗ WP e1 {{ Φ }} ==∗ ▷ |==> ◇ (world σ2 ∗ WP e2 {{ Φ }} ∗ wptp (map (,init_local Λ) efs)).
Proof.
  rewrite {1}wp_unfold /wp_pre. iIntros (Hstep) "[(Hw & HE & Hσ) [H|[_ H]]]".
  { iDestruct "H" as (v) "[% _]". apply val_stuck in Hstep; simplify_eq. }
  rewrite fupd_eq /fupd_def.
  iMod ("H" $! l1 σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame.
  iModIntro; iNext.
  iMod ("H" $! e2 l2 σ2 efs with "[%] [$Hw $HE]") as ">($ & $ & $ & $ & ?)"=>//.
Admitted. (* apparent ... *)

Lemma wptp_step e1 l1 t1 t2 σ1 σ2 Φ :
  step ((e1, l1) :: t1,σ1) (t2, σ2) →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp t1
  ==∗ ∃ e2 l2 t2', ⌜t2 = (e2, l2) :: t2'⌝ ∗ ▷ |==> ◇ (world σ2 ∗ WP e2 {{ Φ }} ∗ wptp t2').
Proof.
  iIntros (Hstep) "(HW & He & Ht)".
  destruct Hstep as [e1' l1' σ1' e2' l2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=.
  - iExists e2', l2', (t2' ++ map (,init_local Λ) efs); iSplitR; first eauto.
    rewrite big_sepL_app. iFrame "Ht". iApply wp_step; try iFrame; eauto.
  - iExists e1, l1, (t1' ++ (e2', l2') :: t2' ++ map (,init_local Λ) efs); iSplitR; first eauto.
    rewrite !big_sepL_app !big_sepL_cons big_sepL_app.
    iDestruct "Ht" as "($ & He' & $)"; iFrame "He". simpl.
    iApply wp_step; try iFrame; eauto.
Qed.

Lemma wptp_steps n e1 l1 t1 t2 σ1 σ2 Φ :
  nsteps step n ((e1, l1) :: t1, σ1) (t2, σ2) →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp t1 ⊢
  Nat.iter (S n) (λ P, |==> ▷ P) (∃ e2 l2 t2',
    ⌜t2 = (e2, l2) :: t2'⌝ ∗ world σ2 ∗ WP e2 {{ Φ }} ∗ wptp t2').
Proof.
  revert e1 l1 t1 t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 l1 t1 t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "?"; eauto 10. }
  iIntros (Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']].
  iMod (wptp_step with "H") as (e1' l1' t1'') "[% H]"; first eauto; simplify_eq.
  iModIntro; iNext; iMod "H" as ">?". by iApply IH.
Qed.

Instance bupd_iter_mono n : Proper ((⊢) ==> (⊢)) (Nat.iter n (λ P, |==> ▷ P)%I).
Proof. intros P Q HP. induction n; simpl; do 2?f_equiv; auto. Qed.

Lemma bupd_iter_frame_l n R Q :
  R ∗ Nat.iter n (λ P, |==> ▷ P) Q ⊢ Nat.iter n (λ P, |==> ▷ P) (R ∗ Q).
Proof.
  induction n as [|n IH]; simpl; [done|].
  by rewrite bupd_frame_l {1}(later_intro R) -later_sep IH.
Qed.

Lemma wptp_result n e1 l1 l2 t1 v2 t2 σ1 σ2 φ :
  nsteps step n ((e1, l1) :: t1, σ1) ((of_val v2, l2) :: t2, σ2) →
  world σ1 ∗ WP e1 {{ v, ⌜φ v⌝ }} ∗ wptp t1 ⊢
  Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜φ v2⌝.
Proof.
  intros. rewrite wptp_steps //.
  rewrite (Nat_iter_S_r (S n)). apply bupd_iter_mono.
  iDestruct 1 as (e2 l2' t2') "(% & (Hw & HE & _) & H & _)"; simplify_eq.
  iDestruct (wp_value_inv with "H") as "H". rewrite fupd_eq /fupd_def.
  iMod ("H" with "[Hw HE]") as ">(_ & _ & $)"; iFrame; auto.
Qed.

Lemma wp_safe e l σ Φ :
  world σ ∗ WP e {{ Φ }} ==∗ ▷ ⌜is_Some (to_val e) ∨ reducible e l σ⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "[(Hw&HE&Hσ) [H|[_ H]]]".
  { iDestruct "H" as (v) "[% _]"; eauto 10. }
  rewrite fupd_eq. iMod ("H" with "* Hσ [-]") as ">(?&?&%&?)"; first by iFrame.
  eauto 10.
Qed.

Lemma wptp_safe n e1 l1 e2 l2 t1 t2 σ1 σ2 Φ :
  nsteps step n ((e1, l1) :: t1, σ1) (t2, σ2) → (e2, l2) ∈ t2 →
  world σ1 ∗ WP e1 {{ Φ }} ∗ wptp t1 ⊢
  Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜is_Some (to_val e2) ∨ reducible e2 l2 σ2⌝.
Proof.
  intros ? He2. rewrite wptp_steps //; rewrite (Nat_iter_S_r (S n)). apply bupd_iter_mono.
  iDestruct 1 as (e2' l2' t2') "(% & Hw & H & Htp)"; simplify_eq.
  apply elem_of_cons in He2 as [?|?]; first (inversion H0; subst; iApply wp_safe; by iFrame "Hw H").
  iApply wp_safe. iFrame "Hw".
  (* iApply (big_sepL_elem_of with "Htp"). *)
Admitted.

Lemma wptp_invariance n e1 l1 e2 t1 t2 σ1 σ2 φ Φ :
  nsteps step n ((e1, l1) :: t1, σ1) (t2, σ2) →
  (state_interp σ2 ={⊤,∅}=∗ ⌜φ⌝) ∗ world σ1 ∗ WP e1 {{ Φ }} ∗ wptp t1
  ⊢ Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜φ⌝.
Proof.
  intros ?. rewrite wptp_steps //.
  rewrite (Nat_iter_S_r (S n)) !bupd_iter_frame_l. apply bupd_iter_mono.
  iIntros "[Hback H]".
  iDestruct "H" as (e2' l2' t2') "(% & (Hw&HE&Hσ) & _)"; subst.
  rewrite fupd_eq.
  iMod ("Hback" with "Hσ [$Hw $HE]") as "> (_ & _ & $)"; auto.
Qed.
End adequacy.

Theorem wp_adequacy Σ Λ `{invPreG Σ} e l σ φ :
  (∀ `{Hinv : invG Σ},
     True ={⊤}=∗ ∃ (stateI : state Λ → iProp Σ) (localI : local_state Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI localI in
       stateI σ ∗ WP e {{ v, ⌜φ v⌝ }}) →
  adequate e l σ φ.
Proof.
  intros Hwp; split.
  - intros t2 l2 σ2 v2 [n ?]%rtc_nsteps.
    eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "".
    rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]".
    rewrite fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate Ilocal) "[HI Hwp]".
    iModIntro. iNext. iApply (@wptp_result _ _ (IrisG _ _ _ Hinv Istate Ilocal)); eauto.
    iFrame. by iApply big_sepL_nil.
  - intros t2 l2 σ2 e2 [n ?]%rtc_nsteps ?.
    eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "".
    rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]".
    rewrite fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
    iDestruct "Hwp" as (Istate Ilocal) "[HI Hwp]".
    iModIntro. iNext. iApply (@wptp_safe _ _ (IrisG _ _ _ Hinv Istate Ilocal)); eauto.
    iFrame. by iApply big_sepL_nil.
Qed.

Theorem wp_invariance Σ Λ `{invPreG Σ} e l σ1 t2 σ2 φ Φ :
  (∀ `{Hinv : invG Σ},
     True ={⊤}=∗ ∃ (stateI : state Λ → iProp Σ) (localI : local_state Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ _ Hinv stateI localI in
       stateI σ1 ∗ WP e {{ Φ }} ∗ (stateI σ2 ={⊤,∅}=∗ ⌜φ⌝)) →
  rtc step ([(e, l)], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n ?]%rtc_nsteps.
  eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "".
  rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]".
  rewrite {1}fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)".
  iDestruct "Hwp" as (Istate Ilocal) "(HIstate & Hwp & Hclose)".
  iModIntro. iNext. iApply (@wptp_invariance _ _ (IrisG _ _ _ Hinv Istate Ilocal)); eauto.
  iFrame "Hw HE Hwp HIstate Hclose". by iApply big_sepL_nil.
Qed.
