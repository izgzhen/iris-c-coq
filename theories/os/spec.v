(* Spec Monoid *)

Require Import logic.
From iris.base_logic Require Import gen_heap.
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

  Definition γ_sstate := @gen_heap_name _ _ _ _ _ specG_spstG.

  Definition sstate (s: spec_state) := ([⋅ map] l ↦ v ∈ s, l S↦ v)%I.
  Definition scode (c: spec_code) := own spec_gname ((1/2)%Qp, (to_agree (c: leibnizC spec_code))).

  Lemma mapsto_singleton l v:
    l S↦ v ⊣⊢ sstate {[ l := v ]}.
  Proof. by rewrite /sstate big_sepM_singleton. Qed.

  Definition spec_inv :=
    (∃ c0 s0 c s,
     scode c ∗ own γ_sstate (● to_gen_heap s) ∗ ⌜ spec_step_star c0 s0 c s⌝)%I.

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
    ⊢ |==> spec_inv ∗ sstate ss' ∗ scode sc'.
  Proof.
    iIntros (?) "(Hinv & Hss & Hsc)".
    iDestruct "Hinv" as (c0 s0 c s) "(HSC & HSS & %)".
    rewrite /sstate /scode.
    (* HSC Hsc and sc' are easy to prove *)
    (* ss, s => ss' are hard, might need some framing properties *)
    iDestruct (sstate_update s ss ss' with "[HSS Hss]") as (s') "(HSS' & Hss' & %)"; first iFrame.
    iMod (scode_update _ _ sc' with "[HSC Hsc]") as "(HSC' & Hsc' & %)"; first iFrame.
    iSplitL "HSS' HSC'".
    { iExists c0, s0, sc', s'. iFrame.
      destruct H2 as (sf & ? & ? & ?).
      subst. iPureIntro.
      eapply SStrans=>//.
      apply spec_step_framing=>//.
    }
    by iFrame.
  Qed.
End rules.
