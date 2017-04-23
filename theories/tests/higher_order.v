Require Import iris_c.clang.logic.

Section example.
  Context `{clangG Σ}.

  Definition abs_spec g E (P Q: iProp Σ) :=
    (∃ gbody, text_interp g (Function Tvoid [] gbody) ∗
              (∀ Φ, P -∗ (Q -∗ Φ Vvoid) -∗ WP gbody @ E {{ Φ }}))%I.

  Lemma higher_order_spec ks E g Φ P Q:
    abs_spec g E P Q ∗ P ∗
    own_stack ks ∗ (own_stack ([]::ks) -∗ Q -∗ Φ Vvoid)
    ⊢ WP Ecall Tvoid g [] @ E {{ Φ }}.
  Proof.
    iIntros "(Hg & HP & Hs & HΦ)".
    iDestruct "Hg" as (e) "[Ht He]".
    iApply (wp_call [] []); last iFrame; first done.
    iNext. iIntros "Hs'".
    iApply ("He" with "HP").
    by iApply "HΦ".
  Qed.

End example.
