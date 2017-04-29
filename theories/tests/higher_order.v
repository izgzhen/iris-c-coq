From iris_c.clang Require Import logic notations.

Section example.
  Context `{clangG Σ}.

  Definition abs_spec g E (P Q: iProp Σ) :=
    (∃ gbody, g T↦ Function Tvoid [] gbody ∗
                (∀ Φ k ks, P -∗ (Q -∗ WP (fill_ectxs void k, ks) {{ Φ }}) -∗
                           WP (gbody, k::ks) @ E {{ Φ }}))%I.

  Lemma higher_order_spec k ks E g Φ P Q:
    abs_spec g E P Q ∗ P ∗ (Q -∗ WP (fill_ectxs void k, ks) {{ Φ }})
    ⊢ WP (fill_ectxs (Ecall Tvoid g []) k, ks) @ E {{ Φ }}.
  Proof.
    iIntros "(Hg & HP & HΦ)".
    iDestruct "Hg" as (e) "[Ht He]".
    iApply (wp_call _ []); last iFrame; first done.
    iNext. iApply ("He" with "HP").
    iApply "HΦ".
  Qed.

End example.
