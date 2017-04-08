From iris_os.clang Require Import logic.

Section wp_ret.
  Context `{clangG Σ}.

  Definition wpr_pre
    (wpr : coPset -c> expr -c> (val -c> iProp Σ) -c> (val -c> iProp Σ) -c> iProp Σ) :
    coPset -c> expr -c> (val -c> iProp Σ) -c> (val -c> iProp Σ) -c> iProp Σ := λ E e1 Φ Φret, (
  (* value case *)
  (∃ v, ⌜to_val e1 = Some v⌝ ∧ Φ v) ∨
  (* local case *)
  (∃ eh K,
     ⌜to_val e1 = None ∧ unfill_expr e1 [] = Some (K, eh) ⌝ ∧
     ((⌜ is_jmp eh = false ⌝ ∗ WP eh @ E {{ v, ▷ wpr E (fill_ectxs (Evalue v) K) Φ Φret }}) ∨
      (⌜ is_jmp eh = true ⌝ ∗ WP eh @ E {{ Φret }}))
  ))%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof. 
    rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
    repeat (f_contractive || f_equiv); apply Hwp.
  Qed.
  
  Local Instance wpr_pre_contractive : Contractive wpr_pre.
  Proof.
    rewrite /wpr_pre=> n wp wp' Hwp E e1 Φ Φret.
    repeat (f_contractive || f_equiv); apply Hwp.
  Qed.
  
  Definition wpr_def:
  coPset → expr → (val → iProp Σ) → (val → iProp Σ) → iProp Σ := fixpoint wpr_pre.
  Definition wpr_aux : { x | x = @wpr_def }. by eexists. Qed.
  Definition wpr := proj1_sig wpr_aux.
  Definition wpr_eq : @wpr = @wpr_def := proj2_sig wpr_aux.

  Lemma wpr_unfold E e Φ Φret : wpr E e Φ Φret ⊣⊢ wpr_pre wpr E e Φ Φret.
  Proof. rewrite wpr_eq. apply (fixpoint_unfold wpr_pre). Qed.

  Lemma wpr_bind kes E e Φ Φret :
    wpr E e (fun v => wpr E (fill_ectxs (Evalue v) kes) Φ Φret) Φret
    ⊢ wpr E (fill_ectxs e kes) Φ Φret.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ Φret). rewrite !wpr_unfold /wp_pre.
    iDestruct "H" as "[H | H]".
    - iDestruct "H" as (v) "[% ?]".
      apply of_to_val in H0. subst.
      by rewrite wpr_unfold /wpr_pre.
    - iDestruct "H" as (eh K) "(% & [[% ?] | [% ?]])"; destruct H0.
      + iRight. iExists eh, (kes ++ K).
        iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iLeft. iSplitL ""; first done.
          iApply (wp_strong_mono E E _ _ _)=>//.
          iFrame. iIntros (?) "?".
          iModIntro. iNext.
          iSpecialize ("IH" $! E (fill_ectxs (Evalue a) K) Φ Φret).
          rewrite fill_app. by iApply "IH".
      + iRight. iExists eh, (kes ++ K). iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iRight. by iSplitL "".
  Qed.
  
End wp_ret.
