From iris_os.clang Require Export logic.
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

Definition step t t' :=
  let '(e, σ, ks) := t in
  let '(e', σ', ks') := t' in
  cstep e σ ks e' σ' ks'.

(* Program logic adequacy *)
Record adequate (e1 : expr) (σ1 : state) (ks: stack) (φ : val → Prop) := {
  adequate_result σ2 ks' v2:
   rtc step (e1, σ1, ks) (Evalue v2, σ2, ks') → φ v2;
  adequate_safe e2 σ2 ks2:
   rtc step (e1, σ1, ks) (e2, σ2, ks2) →
   (is_Some (to_val e2) ∨ reducible e2 σ2 ks2)
}.

(* Theorem adequate_tp_safe {Λ} (e1 : expr Λ) t2 σ1 σ2 φ : *)
(*   adequate e1 σ1 φ → *)
(*   rtc step ([e1], σ1) (t2, σ2) → *)
(*   Forall (λ e, is_Some (to_val e)) t2 ∨ ∃ t3 σ3, step (t2, σ2) (t3, σ3). *)
(* Proof. *)
(*   intros Had ?. *)
(*   destruct (decide (Forall (λ e, is_Some (to_val e)) t2)) as [|Ht2]; [by left|]. *)
(*   apply (not_Forall_Exists _), Exists_exists in Ht2; destruct Ht2 as (e2&?&He2). *)
(*   destruct (adequate_safe e1 σ1 φ Had t2 σ2 e2) as [?|(e3&σ3&efs&?)]; *)
(*     rewrite ?eq_None_not_Some; auto. *)
(*   { exfalso. eauto. } *)
(*   destruct (elem_of_list_split t2 e2) as (t2'&t2''&->); auto. *)
(*   right; exists (t2' ++ e3 :: t2'' ++ efs), σ3; econstructor; eauto. *)
(* Qed. *)

Section adequacy.
Context `{clangG Σ}.
Implicit Types e : expr.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val → iProp Σ.

Notation world σ ks := (wsat ∗ ownE ⊤ ∗ state_interp σ ks)%I.

Lemma wp_step e1 σ1 ks1 e2 σ2 ks2 Φ :
  cstep e1 σ1 ks1 e2 σ2 ks2 →
  world σ1 ks1 ∗ WP e1 {{ Φ }} ==∗ ▷ |==> ◇ (world σ2 ks2 ∗ WP e2 {{ Φ }}).
Proof.
(*   rewrite {1}wp_unfold /wp_pre. iIntros (Hstep) "[(Hw & HE & Hσ) [H|[_ H]]]". *)
(*   { iDestruct "H" as (v) "[% _]". apply val_stuck in Hstep; simplify_eq. } *)
(*   rewrite fupd_eq /fupd_def. *)
(*   iMod ("H" $! σ1 with "Hσ [Hw HE]") as ">(Hw & HE & _ & H)"; first by iFrame. *)
(*   iModIntro; iNext. *)
(*   by iMod ("H" $! e2 σ2 efs with "[%] [$Hw $HE]") as ">($ & $ & $ & $)". *)
(* Qed. *) Admitted.

Lemma wptp_step e1 e2 σ1 σ2 ks1 ks2 Φ :
  step (e1, σ1, ks1) (e2, σ2, ks2) →
  world σ1 ks1 ∗ WP e1 {{ Φ }}
  ==∗ ▷ |==> ◇ (world σ2 ks2 ∗ WP e2 {{ Φ }}).
Proof.
(*   iIntros (Hstep) "(HW & He & Ht)". *)
(*   destruct Hstep as [e1' σ1' e2' σ2' efs [|? t1'] t2' ?? Hstep]; simplify_eq/=. *)
(*   - iExists e2', (t2' ++ efs); iSplitR; first eauto. *)
(*     rewrite big_sepL_app. iFrame "Ht". iApply wp_step; try iFrame; eauto. *)
(*   - iExists e, (t1' ++ e2' :: t2' ++ efs); iSplitR; first eauto. *)
(*     rewrite !big_sepL_app !big_sepL_cons big_sepL_app. *)
(*     iDestruct "Ht" as "($ & He' & $)"; iFrame "He". *)
(*     iApply wp_step; try iFrame; eauto. *)
(* Qed. *) Admitted.

Lemma wptp_steps n e1 e2 σ1 σ2 ks1 ks2 Φ :
  nsteps step n (e1, σ1, ks2) (e2, σ2, ks2) →
  world σ1 ks1 ∗ WP e1 {{ Φ }}  ⊢
  Nat.iter (S n) (λ P, |==> ▷ P)
  (world σ2 ks2 ∗ WP e2 {{ Φ }}).
Proof.
(*   revert e1 t1 t2 σ1 σ2; simpl; induction n as [|n IH]=> e1 t1 t2 σ1 σ2 /=. *)
(*   { inversion_clear 1; iIntros "?"; eauto 10. } *)
(*   iIntros (Hsteps) "H". inversion_clear Hsteps as [|?? [t1' σ1']]. *)
(*   iMod (wptp_step with "H") as (e1' t1'') "[% H]"; first eauto; simplify_eq. *)
(*   iModIntro; iNext; iMod "H" as ">?". by iApply IH. *)
(* Qed. *) Admitted.

Instance bupd_iter_mono n : Proper ((⊢) ==> (⊢)) (Nat.iter n (λ P, |==> ▷ P)%I).
Proof. intros P Q HP. induction n; simpl; do 2?f_equiv; auto. Qed.

Lemma bupd_iter_frame_l n R Q :
  R ∗ Nat.iter n (λ P, |==> ▷ P) Q ⊢ Nat.iter n (λ P, |==> ▷ P) (R ∗ Q).
Proof.
  induction n as [|n IH]; simpl; [done|].
  by rewrite bupd_frame_l {1}(later_intro R) -later_sep IH.
Qed.

Lemma wptp_result n e1 v2 σ1 σ2 ks1 ks2 φ :
  nsteps step n (e1, σ1, ks1) (Evalue v2, σ2, ks2) →
  world σ1 ks1 ∗ WP e1 {{ v, ⌜φ v⌝ }}  ⊢
  Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜φ v2⌝.
Proof.
(*   intros. rewrite wptp_steps //. *)
(*   rewrite (Nat_iter_S_r (S n)). apply bupd_iter_mono. *)
(*   iDestruct 1 as (e2 t2') "(% & (Hw & HE & _) & H & _)"; simplify_eq. *)
(*   iDestruct (wp_value_inv with "H") as "H". rewrite fupd_eq /fupd_def. *)
(*   iMod ("H" with "[Hw HE]") as ">(_ & _ & $)"; iFrame; auto. *)
(* Qed. *) Admitted.

Lemma wp_safe e σ ks Φ :
  world σ ks ∗ WP e {{ Φ }} ==∗ ▷ ⌜is_Some (to_val e) ∨ reducible e σ ks⌝.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "[(Hw&HE&Hσ) [H|[_ H]]]".
  { iDestruct "H" as (v) "[% _]"; eauto 10. }
  rewrite fupd_eq. iMod ("H" with "* Hσ [-]") as ">(?&?&%&?)"; first by iFrame.
  eauto 10.
Qed.

Lemma wptp_safe n e1 e2 σ1 σ2 ks1 ks2 Φ :
  nsteps step n (e1, σ1, ks1) (e2, σ2, ks2) →
  world σ1 ks1 ∗ WP e1 {{ Φ }} ⊢
  Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜is_Some (to_val e2) ∨ reducible e2 σ2 ks2⌝.
Proof.
(*   intros ? He2. rewrite wptp_steps //; rewrite (Nat_iter_S_r (S n)). apply bupd_iter_mono. *)
(*   iDestruct 1 as (e2' t2') "(% & Hw & H & Htp)"; simplify_eq. *)
(*   apply elem_of_cons in He2 as [<-|?]; first (iApply wp_safe; by iFrame "Hw H"). *)
(*   iApply wp_safe. iFrame "Hw". by iApply (big_sepL_elem_of with "Htp"). *)
(* Qed. *) Admitted.

Lemma wptp_invariance n e1 e2 σ1 σ2 ks1 ks2 φ Φ :
  nsteps step n (e1, σ1, ks1) (e2, σ2, ks2) →
  (state_interp σ2 ks2 ={⊤,∅}=∗ ⌜φ⌝) ∗ world σ1 ks1 ∗ WP e1 {{ Φ }}
  ⊢ Nat.iter (S (S n)) (λ P, |==> ▷ P) ⌜φ⌝.
Proof.
(*   intros ?. rewrite wptp_steps //. *)
(*   rewrite (Nat_iter_S_r (S n)) !bupd_iter_frame_l. apply bupd_iter_mono. *)
(*   iIntros "[Hback H]". *)
(*   iDestruct "H" as (e2' t2') "(% & (Hw&HE&Hσ) & _)"; subst. *)
(*   rewrite fupd_eq. *)
(*   iMod ("Hback" with "Hσ [$Hw $HE]") as "> (_ & _ & $)"; auto. *)
(* Qed. *) Admitted.

End adequacy.

Theorem wp_adequacy Σ `{clangG Σ, invPreG Σ} e σ ks φ :
  (True ={⊤}=∗ state_interp σ ks ∗ WP e {{ v, ⌜φ v⌝ }}) →
  adequate e σ ks φ.
Proof.
  (* intros Hwp; split. *)
  (* - intros t2 σ2 v2 [n ?]%rtc_nsteps. *)
  (*   eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "". *)
  (*   rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]". *)
  (*   rewrite fupd_eq in Hwp; iMod (Hwp with "[Hw HE]") as ">Hwp";  *)
    
  (*   iDestruct "Hwp" as (Istate) "[HI Hwp]". *)
  (*   iModIntro. iNext. iApply (@wptp_result _ _ (IrisG _ _ Hinv Istate)); eauto. *)
  (*   iFrame. by iApply big_sepL_nil. *)
  (* - intros t2 σ2 e2 [n ?]%rtc_nsteps ?. *)
  (*   eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "". *)
  (*   rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]". *)
  (*   rewrite fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)". *)
  (*   iDestruct "Hwp" as (Istate) "[HI Hwp]". *)
  (*   iModIntro. iNext. iApply (@wptp_safe _ _ (IrisG _ _ Hinv Istate)); eauto. *)
  (*   iFrame. by iApply big_sepL_nil. *)
Admitted.

Theorem wp_invariance Σ `{clangG Σ, invPreG Σ} e σ1 e2 σ2 ks1 ks2 φ Φ :
  (True ={⊤}=∗ state_interp σ1 ks1 ∗ WP e {{ Φ }} ∗ (state_interp σ2 ks2 ={⊤,∅}=∗ ⌜φ⌝)) →
  rtc step (e, σ1, ks1) (e2, σ2, ks2) →
  φ.
Proof.
(*   intros Hwp [n ?]%rtc_nsteps. *)
(*   eapply (soundness (M:=iResUR Σ) _ (S (S (S n)))); iIntros "". *)
(*   rewrite Nat_iter_S. iMod wsat_alloc as (Hinv) "[Hw HE]". *)
(*   rewrite {1}fupd_eq in Hwp; iMod (Hwp with "[$Hw $HE]") as ">(Hw & HE & Hwp)". *)
(*   iDestruct "Hwp" as (Istate) "(HIstate & Hwp & Hclose)". *)
(*   iModIntro. iNext. iApply (@wptp_invariance _ _ (IrisG _ _ Hinv Istate)); eauto. *)
(*   iFrame "Hw HE Hwp HIstate Hclose". by iApply big_sepL_nil. *)
(* Qed. *)
Admitted.

Class clangPreG Σ := ClangPreG {
  clang_preG_iris :> invPreG Σ;
  clang_preG_clang :> gen_heapPreG addr val Σ;
  clangG_preG_textG :> inG Σ (authR (gmapUR ident (agreeR (discreteC function))));
  clangG_preG_stackG :> inG Σ (prodR fracR (agreeR (discreteC stack)));
}.

(* Definition heapΣ : gFunctors := #[invΣ; gen_heapΣ loc val]. *)
(* Instance subG_heapPreG {Σ} : subG heapΣ Σ → heapPreG Σ. *)
(* Proof. solve_inG. Qed. *)

Definition clang_adequacy Σ `{clangPreG Σ} e σ ks φ :
  (∀ `{clangG Σ}, True ⊢ WP e {{ v, ⌜φ v⌝ }}) →
  adequate e σ ks φ.
Proof.
(*   intros Hwp; eapply (wp_adequacy _ _); iIntros (?) "". *)
(*   iMod (own_alloc (● to_gen_heap σ)) as (γ) "Hh". *)
(*   { apply: auth_auth_valid. exact: to_gen_heap_valid. } *)
(*   iModIntro. iExists (λ σ, own γ (● to_gen_heap σ)); iFrame. *)
(*   set (Hheap := GenHeapG loc val Σ _ _ _ γ). *)
(*   iApply (Hwp (HeapG _ _ _)). *)
(* Qed. *)
Admitted.
