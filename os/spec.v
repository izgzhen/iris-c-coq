(* Spec Monoid *)

Require Import logic.
From iris.base_logic Require Import gen_heap.
From iris.base_logic Require Export big_op.
From iris.algebra Require Import gmap agree auth.
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
    ∀ (r: spec_rel) s retv s',
      r s retv s' → spec_step (SCrel r) s (SCdone retv) s'.

(* Naive equivalence *)
Instance spec_code_equiv: Equiv spec_code := (=).

Class specG Σ := SpecG {
  specG_spstG :> gen_heapG ident val Σ;
  specG_specG :> inG Σ (authR (optionUR (agreeR (discreteC (spec_code)))));
  spec_gname : gname
}.

Notation "l S↦ v" :=
  (@mapsto _ _ _ _ _ specG_spstG l 1%Qp v) (at level 20) : uPred_scope.

Section rules.
  Context `{specG Σ}.

  Definition γ_sstate := @gen_heap_name _ _ _ _ _ specG_spstG.

  Definition sstate (s: spec_state) := ([⋅ map] l ↦ v ∈ s, l S↦ v)%I.
  Definition scode (c: spec_code) := own spec_gname (◯ (Some (to_agree (c: leibnizC spec_code)))).
  
  Definition spec_inv :=
    (∃ c0 s0 c s,
     own spec_gname (● (Some (to_agree (c : leibnizC spec_code)))) ∗
     own γ_sstate (● to_gen_heap s) ∗ ⌜ spec_step c0 s0 c s⌝)%I.

  Lemma spec_step_framing c c' sf s s':
    gset_dom sf ⊥ gset_dom s → spec_step c s c' s' → spec_step c (sf ∪ s) c' (sf ∪ s').
  Admitted.

  Lemma spec_step_trans c c' c'' s s' s'':
    spec_step c s c' s' → spec_step c' s' c'' s'' → spec_step c s c'' s''.
  Admitted.

  Lemma sstate_update s ss ss':
    own γ_sstate (● to_gen_heap s) ∗
    ([∗ map] l↦v ∈ ss, l S↦ v)
    ⊢ (∃ s', own γ_sstate (● to_gen_heap s') ∗
             ([∗ map] l↦v ∈ ss', l S↦ v) ∗
             ⌜ ∃ sf, gset_dom sf ⊥ gset_dom ss ∧ s = sf ∪ ss ∧ s' = sf ∪ ss' ⌝).
  Proof.
  Admitted.

  Lemma scode_update c1 c2 c3:
    own spec_gname (● Some (to_agree c1)) ∗
    own spec_gname (◯ Some (to_agree c2))
    ⊢ own spec_gname (● Some (to_agree c3)) ∗
      own spec_gname (◯ Some (to_agree c3)) ∗ ⌜ c1 = c2 ⌝.
  Admitted.
    
  Lemma spec_update ss sc ss' sc':
    spec_inv ∗ sstate ss ∗ scode sc ∗
    ⌜ spec_step sc ss sc' ss' ⌝
    ⊢ spec_inv ∗ sstate ss' ∗ scode sc'.
  Proof.
    iIntros "(Hinv & Hss & Hsc & %)".
    iDestruct "Hinv" as (c0 s0 c s) "(HSC & HSS & %)".
    rewrite /sstate /scode.
    (* HSC Hsc and sc' are easy to prove *)
    (* ss, s => ss' are hard, might need some framing properties *)
    iDestruct (sstate_update s ss ss' with "[HSS Hss]") as (s') "(HSS' & Hss' & %)"; first iFrame.
    iDestruct (scode_update _ _ sc' with "[HSC Hsc]") as "(HSC' & Hsc' & %)"; first iFrame.
    iSplitL "HSS' HSC'".
    { iExists c0, s0, sc', s'. iFrame.
      destruct H2 as (sf & ? & ? & ?).
      subst. iPureIntro.
      assert (spec_step sc (sf ∪ ss) sc' (sf ∪ ss')) as ?; first by apply spec_step_framing.
      eapply spec_step_trans=>//.
    }
    iFrame.
  Qed.
End rules.
