Require Import logic.
From iris.base_logic Require Import soundness gen_heap.
From iris.base_logic Require Export big_op.
From iris.algebra Require Import dra gmap agree auth frac.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.
From iris_os.os Require Export spec refine_ra.
Set Default Proof Using "Type".
Import uPred.

Instance equiv_cfg: Equiv cfg := (=).

Definition specM := (prodR fracR (agreeR (discreteC cfg))).

Class specG K Σ := SpecG {
    specG_cfgG :> inG Σ specM;
    cfgG_gname : gname;
    refine_inG :> inG Σ (@refine_ucmra K);
    refine_gname : gname
}.

Section specG.
  Context `{specG K Σ}.

  Definition refine v cs : refine_ucmra := to_validity (Refine K v cs).

  Definition master_own_exact cs := own refine_gname (refine master cs).

  Definition master_own c := (∃ cs, own refine_gname (refine master (c :: cs)))%I.

  Definition snapshot_own_exact cs := own refine_gname (refine snapshot cs).

  Definition snapshot_own c := (∃ cs, own refine_gname (refine snapshot (c :: cs)))%I.

  Lemma valid_refine_op cs1 cs2:
    ✓ (refine master cs1 ⋅ refine snapshot cs2) →
    ∃ cs, cs1 = cs ++ cs2.
  Proof. intros (?&?&Hdisj). inversion Hdisj. eauto. Qed.

  Lemma refine_snap':
    ∀ cs,
      master_own_exact cs ⊢ |==> own refine_gname (refine master cs ⋅ refine snapshot cs).
  Proof.
    iIntros. iApply own_update; last done.
    intros x mz Hm.
    destruct mz eqn:Heq.
    - destruct Hm as [? [? ?]].
      try repeat split=>//; simpl.
      + apply refine_disj'.
      + by rewrite refine_op'.
    - simpl. split; [|split]=>//. apply refine_disj'.
  Qed.

  Lemma refine_snap:
    ∀ c,
      master_own c ⊢ |==> master_own c ∗ snapshot_own c.
  Proof.
    iIntros (c) "Hm". iDestruct "Hm" as (cs) "Hm".
    iMod (refine_snap' with "Hm") as "[Hm Hs]".
    iSplitL "Hm"; by iExists _.
  Qed.

  Lemma master_grow':
    ∀ c0 c cs,
      spec_step' c0 c →
      master_own_exact (c0::cs) ⊢ |==> master_own_exact (c::c0::cs).
  Proof.
    iIntros (????) "H". iApply own_update; last done.
    intros x mz Hm.
    destruct mz eqn:Heq.
    - destruct Hm as [? [? ?]].
      try repeat split=>//; simpl.
      + constructor=>//.
      + inversion H3. subst.
        replace (c :: cs2 ++ cs1) with ((c :: cs2) ++ cs1)=>//.
        constructor.
    - simpl. constructor=>//.
  Qed.

  Lemma master_grow:
    ∀ c c',
      spec_step' c c' →
      master_own c ⊢ |==> master_own c'.
  Proof.
    iIntros (???) "Ho".
    iDestruct "Ho" as (?) "Ho".
    iExists _. iApply master_grow'=>//.
  Qed.

  Definition to_cfgM (c: cfg) : specM :=
    ((1/2)%Qp, (to_agree (c: leibnizC cfg))).
  
  Definition own_cfg (c: cfg) := own cfgG_gname (to_cfgM c).

  Definition spec_inv := (∃ c, own_cfg c ∗ master_own c)%I.

  Global Instance spec_inv_timeless: TimelessP spec_inv. Proof. apply _. Qed.
  
  Lemma own_cfg_agree ks ks':
   own_cfg ks ∗ own_cfg ks'  ⊢ ⌜ ks = ks' ⌝.
  Proof.
    iIntros "[Hs' Hs]".
    rewrite /own_cfg.
    iDestruct (own_valid_2 with "Hs Hs'") as "%".
    iPureIntro. destruct H0 as [? ?]. simpl in H1.
    by apply to_agree_comp_valid in H1.
  Qed.

  Lemma own_cfg_update c1 c2 c3:
    own_cfg c1 ∗ own_cfg c2 ⊢ |==> own_cfg c3 ∗ own_cfg c3 ∗ ⌜ c1 = c2 ⌝.
  Proof.
    iIntros "[Hs Hs']".
    iDestruct (own_cfg_agree with "[-]") as "%"; first iFrame.
    inversion H0. subst.
    rewrite /own_cfg.
    iMod (own_update_2 with "Hs Hs'") as "[Hs Hs']"; last by iFrame.
    rewrite pair_op frac_op' Qp_div_2.
    apply cmra_update_exclusive.
    split; simpl.
    - by rewrite frac_op'.
    - by apply to_agree_comp_valid.
  Qed.

  Lemma spec_update c c':
    spec_step' c c' →
    spec_inv ∗ own_cfg c ∗ snapshot_own c
    ⊢ |==> spec_inv ∗ own_cfg c' ∗ snapshot_own c'.
  Proof.
    iIntros (?) "(Hinv & Hc & _)".
    iDestruct "Hinv" as (c'') "(HC & Hm)".
    iMod (own_cfg_update _ _ c' with "[HC Hc]") as "(HC' & Hc' & %)"; first iFrame.
    iFrame. subst.
    iMod (master_grow _ c' with "Hm") as "Hm'"=>//.
    iMod (refine_snap with "Hm'") as "[Hm' Hs']".
    iFrame. iExists _. by iFrame.
  Qed.
  
End specG.
