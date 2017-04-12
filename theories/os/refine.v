Require Import logic.
From iris.base_logic Require Import soundness gen_heap.
From iris.base_logic Require Export big_op.
From iris.algebra Require Import dra gmap agree auth frac.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.
From iris_os.os Require Export spec refine_ra.
From iris_os.lib Require Import pair.
Set Default Proof Using "Type".
Import uPred.

Class specG K Σ := SpecG {
    refine_inG :> inG Σ (@refine_ucmra K);
    refine_specG :> @pairG spec_code Σ;
    refine_spstG :> @pairG spec_state Σ;
    refine_gname : gname;
    spst_gname : gname;
    spec_gname : gname;
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

  Definition own_sstate := @own_pair spec_state Σ refine_spstG spst_gname.
  Definition update_sstate :=  @own_pair_update spec_state Σ refine_spstG spst_gname.
  Definition own_scode := @own_pair spec_code Σ refine_specG spec_gname.
  Definition update_scode :=  @own_pair_update spec_code Σ refine_specG spec_gname.
  
  Definition spec_inv := (∃ ss sc, own_sstate ss ∗ own_scode sc ∗ master_own (ss, sc))%I.

  Global Instance spec_inv_timeless: TimelessP spec_inv. Proof. apply _. Qed.

  Lemma spec_update {sc sc'} ss ss':
    spec_step sc ss sc' ss' →
    spec_inv ∗ own_sstate ss ∗ own_scode sc
    ⊢ |==> spec_inv ∗ own_sstate ss' ∗ own_scode sc' ∗ snapshot_own (ss', sc').
  Proof.
    iIntros (?) "(Hinv & Hss & Hsc)".
    iDestruct "Hinv" as (ss'' sc'') "(HSS & HSC & Hm)".
    unfold own_scode, own_sstate.
    iMod (update_scode _ _ sc' with "[HSC Hsc]") as "(HSC' & Hsc' & %)"; first iFrame.
    iMod (update_sstate _ _ ss' with "[HSS Hss]") as "(HSS' & Hss' & %)"; first iFrame.
    subst. iFrame.
    iMod (master_grow _ (ss', sc') with "Hm") as "Hm'"=>//.
    iMod (refine_snap with "Hm'") as "[Hm' Hs']".
    iFrame. iExists _, _. by iFrame.
  Qed.
  
End specG.
