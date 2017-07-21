From iris_c.clang Require Import logic notations.

Section example.
  Context `{clangG Σ}.

  Definition abs_spec g E (P Q: iProp Σ) :=
    (∃ gbody, g T↦ Function Tvoid [] gbody ∗
                (∀ Φ k ks Ω, P -∗ (Q -∗ WP (fill_ectxs void k, (ks, Ω)) {{ Φ }}) -∗
                             WP (gbody, (Kcall k Ω::ks, semp)) @ E {{ Φ }}))%I.

  Lemma higher_order_spec k ks E g Φ P Q Ω:
    abs_spec g E P Q ∗ P ∗ (Q -∗ WP (fill_ectxs void k, (ks, Ω)) {{ Φ }})
    ⊢ WP (fill_ectxs (Ecall Tvoid g Vvoid) k, (ks, Ω)) @ E {{ Φ }}.
  Proof.
    iIntros "(Hg & HP & HΦ)".
    iDestruct "Hg" as (e) "[Ht He]".
    iApply (wp_call semp Ω _ Vvoid); last iFrame; first done.
    iNext. iApply ("He" with "HP").
    iApply "HΦ".
  Qed.

End example.
