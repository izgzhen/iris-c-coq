From iris_c.clang Require Import logic notations tactics.
From iris.base_logic.lib Require Export namespaces invariants.
From iris_c.clang.lib Require Import interrupt.

Section example.
  Context `{clangG Σ} {N': namespace}.

  Definition invs (prio: nat) : iProp Σ := False%I.

  Context `{i: interrupt invs 1}.

  Variable l: addr.

  Definition f_body : expr :=
    l <- vfalse.

  Lemma ct_spec ks:
    inv N' True%I ∗
    l ↦ vtrue @ tybool ∗ "f" T↦ Function Tvoid [] f_body
    ⊢ WP (create_task i "f" 0, ks) {{ _, True%I }}.
  Proof.
    iIntros "[#HI [Hl Hf]]".
    iApply create_task_spec.
    iFrame. iIntros (N). simpl.
    iIntros "% [H1 H0]".
    iApply (wp_atomic (⊤ ∖ ↑N) (⊤ ∖ ↑N ∖ ↑N')).
    { by apply atomic_enf. }
    assert (N ⊥ N').
    { apply H0. }
    iInv (N') as "?" "Hclose".
    iModIntro. iApply (@wp_assign _ _ _ _ vtrue vfalse tybool tybool)=>//; constructor.
  Qed.

End example.
