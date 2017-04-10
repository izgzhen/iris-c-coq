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
     ((⌜ is_jmp eh = false ⌝ ∗ WP eh @ E {{ v, wpr E (fill_ectxs (Evalue v) K) Φ Φret }}) ∨
      (∃ v, ⌜ eh = Erete (Evalue v) ⌝ ∗ (stack_interp [[]] -∗ WP (Evalue v) @ E {{ Φret }})) ∨
      (∃ f ls, ⌜ eh = Ecall f (map (λ l : addr, Evalue (Vptr l)) ls) ⌝ ∗
               (stack_interp [[]] -∗
                WP eh @ E {{ v, ▷ wpr E (fill_ectxs (Evalue v) K) Φ Φret }})))
  ))%I.

  Local Instance wpr_pre_contractive : Contractive wpr_pre.
  Proof.
    rewrite /wpr_pre=> n wp wp' Hwp E e1 Φ Φret.
    (* repeat (f_contractive || f_equiv); apply Hwp. *)
  Admitted.

  Definition wpr_def:
  coPset → expr → (val → iProp Σ) → (val → iProp Σ) → iProp Σ := fixpoint wpr_pre.
  Definition wpr_aux : { x | x = @wpr_def }. by eexists. Qed.
  Definition wpr := proj1_sig wpr_aux.
  Definition wpr_eq : @wpr = @wpr_def := proj2_sig wpr_aux.

  Lemma wpr_unfold E e Φ Φret : wpr E e Φ Φret ⊣⊢ wpr_pre wpr E e Φ Φret.
  Proof. rewrite wpr_eq. apply (fixpoint_unfold wpr_pre). Qed.

  Lemma wpr_helper E P R Q e eh K:
    unfill_expr e [] = Some (K, eh) →
    (∀ v, P v ∗ R ⊢ Q v) →
    ▷ R ∗
    WP eh @ E {{ P }}
    ⊢ WP eh @ E {{ Q }}.
  Proof.
    iIntros (??) "[HR ?]".
    assert (to_val eh = None) as ?; first admit.
    iDestruct (wp_frame_step_l' with "[-]") as "?"=>//.
    { iFrame "HR". iFrame. }
    iApply (wp_strong_mono E E)=>//.
    iFrame. iIntros (?) "[? ?]".
    iModIntro. iApply H1. iFrame.
  Admitted.

  Lemma wpr_bind kes E e Φ Φret :
    wpr E e (fun v => wpr E (fill_ectxs (Evalue v) kes) Φ Φret) Φret
    ⊢ wpr E (fill_ectxs e kes) Φ Φret.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ Φret). rewrite !wpr_unfold /wp_pre.
    iDestruct "H" as "[H | H]".
    - iDestruct "H" as (v) "[% ?]".
      apply of_to_val in H0. subst.
      by rewrite wpr_unfold /wpr_pre.
    - iDestruct "H" as (eh K) "(% & [[% ?]| [? | ?]])"; destruct H0.
      + iRight. iExists eh, (kes ++ K).
        iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iLeft. iSplitL ""; first done.
          iApply wpr_helper=>//; last (iFrame "IH"; iFrame).
          iIntros (?) "[? ?]".
          iSpecialize ("~1" $! E (fill_ectxs (Evalue _) K) Φ Φret).
          rewrite fill_app. by iApply "~1".
      + iDestruct "~" as (v) "[% ?]". iRight. iExists eh, (kes ++ K). iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iRight. iLeft. iExists v. by iSplitL "".
      + iDestruct "~" as (??) "[% ?]".
        iRight. iExists eh, (kes ++ K). iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iRight. iRight. iExists H2, H3.
          iSplitL ""; first done. iIntros "?".
          iDestruct ("~1" with "~") as "?".
          iApply (wp_strong_mono E E)=>//.
          iFrame. iIntros (?) "?".
          iModIntro. iNext.
          iSpecialize ("IH" $! E (fill_ectxs (Evalue a) K)).
          rewrite fill_app. by iApply "IH".
  Qed.

  Lemma wpr_ret v E Φ Φret:
    Φret v ⊢ wpr E (Erete (Evalue v)) Φ Φret.
  Proof.
    iIntros "H".
    rewrite wpr_unfold /wpr_pre.
    iRight. iExists (Erete (Evalue v)), [].
    iSplit.
    - iPureIntro. split=>//.
    - iRight. iLeft. iExists v. iSplitL ""; first done.
      iIntros "?".
      by iApply wp_value.
  Qed.

  Lemma wp_something E e Φ:
    wpr E e (λ _ : val, False) Φ
    ⊢ WP e @ E {{ v, Φ v }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ). rewrite !wpr_unfold /wp_pre.
    iDestruct "H" as "[H | H]".
    - by iDestruct "H" as (v) "[_ %]".
    - iDestruct "H" as (eh K) "(% & [[% ?]| [? | ?]])"; destruct H0.
      + assert (e = fill_ectxs eh K) as ?; first admit.
        subst. iApply wp_bind=>//.
        iApply wpr_helper=>//; last (iFrame "IH"; iFrame).
        iIntros (v) "[? IH]".
        by iApply "IH".
      + iDestruct "~" as (v) "[% ?]".
        subst. assert (e = fill_ectxs (Erete (Evalue v)) K) as ?; first admit.
        subst. iApply (wp_ret _ [] [[]]).
        iSplitL ""; first admit.
        iIntros "?".
        simpl. by iDestruct ("~1" with "~") as "?".
      + iDestruct "~" as (f ls) "[% ?]".
        assert (e = fill_ectxs eh K) as ?; first admit. subst.
        iAssert (stack_interp [[]]) as "H"; first admit.
        iDestruct ("~1" with "H") as "?".
        admit.
  Admitted.

  Lemma wpr_call E es ls params f_body f_body' f retty Φ Φret:
    es = map (fun l => Evalue (Vptr l)) ls →
    instantiate_f_body (add_params_to_env (Env [] []) params ls) f_body = Some f_body' →
    text_interp f (Function retty params f_body) ∗
    ▷ wpr E f_body' (fun _ => False%I) Φ
    ⊢ wpr E (Ecall f es) Φ Φret.
  Proof.
    iIntros (??) "[? ?]".
    iApply wpr_unfold. rewrite /wpr_pre.
    iRight. iExists (Ecall f es), [].
    iSplit.
    { iPureIntro. split=>//. simpl.
      subst. by rewrite forall_is_val. }
    iRight. iRight. iExists f, ls. subst. iSplitL ""; first done.
    iIntros "?".
    iApply (wp_call _ [])=>//.
    iFrame. iNext. iIntros "?".
    simpl. iApply wp_something.
  Admitted.

End wp_ret.
