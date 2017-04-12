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

Class specG K Σ := SpecG {
    specG_spstG :> gen_heapG ident val Σ;
    specG_specG :> inG Σ (prodR fracR (agreeR (discreteC (spec_code))));
    spec_gname : gname;
    refine_inG :> inG Σ (@refine_ucmra K);
    refine_gname : gname
}.

Notation "l S↦ v" :=
  (@mapsto _ _ _ _ _ specG_spstG l 1%Qp v) (at level 20) : uPred_scope.

Section specG.
  Context `{specG K Σ}.

  Definition refine v cs : refine_ucmra := to_validity (Refine K v cs).

  Definition master_own_exact cs := own refine_gname (refine master cs).

  Definition snapshot_own_exact cs := own refine_gname (refine snapshot cs).

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

  Lemma spec_grow:
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

  Definition γ_sstate := @gen_heap_name _ _ _ _ _ specG_spstG.

  Definition sstate (s: spec_state) := ([⋅ map] l ↦ v ∈ s, l S↦ v)%I.
  Definition scode (c: spec_code) := own spec_gname ((1/2)%Qp, (to_agree (c: leibnizC spec_code))).

  Lemma mapsto_singleton l v:
    l S↦ v ⊣⊢ sstate {[ l := v ]}.
  Proof. by rewrite /sstate big_sepM_singleton. Qed.

  Definition spec_inv :=
    (∃ c0 s0 c s cs,
       scode c ∗ own γ_sstate (● to_gen_heap s) ∗
       master_own_exact ((s, c)::cs) ∗ ⌜ spec_step_star c0 s0 c s ⌝)%I.

  Global Instance spec_inv_timeless: TimelessP spec_inv. Proof. apply _. Qed.

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

  Lemma spec_update {sc sc'} ss ss':
    spec_step sc ss sc' ss' →
    spec_inv ∗ sstate ss ∗ scode sc
    ⊢ |==> (∃ cs, spec_inv ∗ sstate ss' ∗ scode sc' ∗ snapshot_own_exact ((ss', sc')::(ss, sc)::cs)).
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
    spec_inv ∗ sstate ss ∗ scode sc ∗ snapshot_own_exact ((ss0, sc0)::cs)
    ⊢ ⌜ spec_step_star sc0 ss0 sc ss ⌝.
  Admitted.

End specG.
