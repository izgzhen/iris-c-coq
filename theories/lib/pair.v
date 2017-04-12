Require Import logic.
From iris.algebra Require Import agree frac.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Section defs.
  Context {t: Type}.

  Local Instance t_equiv: Equiv t := (=).

  Definition pairM := (prodR fracR (agreeR (discreteC t))).

  Class pairG (Σ: gFunctors) := pair_inG :> inG Σ pairM.

  Definition to_pairM c : pairM := ((1/2)%Qp, (to_agree (c: leibnizC t))).

End defs.

Section rules.
  Context `{@pairG t Σ} {γ: gname}.
  
  Definition own_pair (c: t) := own γ (to_pairM c).

  Lemma own_pair_agree ks ks':
   own_pair ks ∗ own_pair ks'  ⊢ ⌜ ks = ks' ⌝.
  Proof.
    iIntros "[Hs' Hs]".
    rewrite /own_update.
    iDestruct (own_valid_2 with "Hs Hs'") as "%".
    iPureIntro. destruct H0 as [? ?]. simpl in H1.
    by apply to_agree_comp_valid in H1.
  Qed.

  Lemma own_pair_update c1 c2 c3:
    own_pair c1 ∗ own_pair c2 ⊢ |==> own_pair c3 ∗ own_pair c3 ∗ ⌜ c1 = c2 ⌝.
  Proof.
    iIntros "[Hs Hs']".
    iDestruct (own_pair_agree with "[-]") as "%"; first iFrame.
    inversion H0. subst.
    rewrite /own_update.
    iMod (own_update_2 with "Hs Hs'") as "[Hs Hs']"; last by iFrame.
    rewrite pair_op frac_op' Qp_div_2.
    apply cmra_update_exclusive.
    split; simpl.
    - by rewrite frac_op'.
    - by apply to_agree_comp_valid.
  Qed.

End rules.
