From iris_c.clang Require Import notations ret_logic ret_tactics.

Section example.
  Context `{clangG Σ}.

  Definition one : expr := Int.repr 1.

  Definition ret_one : expr := return: Vint32 (Int.repr 1) ;; return: Vint32 (Int.repr 2).

  Lemma one_spec E:
    True%I ⊢ wpr E one (λ v, ⌜ v = Vint32 (Int.repr 1) ⌝) (λ _, False%I).
  Proof. by iApply wpr_value. Qed.

  Lemma ret_one_spec E:
    True%I ⊢ wpr E ret_one (λ _, False%I) (λ v, ⌜ v = Vint32 (Int.repr 1) ⌝).
  Proof.
    unfold ret_one. iApply wpr_seq.
    by iApply wpr_ret.
  Qed.

End example.
