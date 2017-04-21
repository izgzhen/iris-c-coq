From iris_c.clang Require Import notations ret_logic ret_tactics.
Require Import iris_c.lib.int.

Section example.
  Context `{clangG Σ}.

  Lemma one_spec E:
    True%I ⊢ wpr E 1 (λ v, ⌜ v = 1 ⌝) (λ _, False%I).
  Proof. by iApply wpr_value. Qed.

  Lemma ret_one_spec E:
    True%I ⊢ wpr E (return: 1 ;; return: 1) (λ _, False%I) (λ v, ⌜ v = 1 ⌝).
  Proof. iApply wpr_seq. by iApply wpr_ret. Qed.

End example.
