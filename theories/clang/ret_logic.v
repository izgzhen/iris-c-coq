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
      (∃ v, ⌜ eh = Erete (Evalue v) ⌝ ∗ ▷ Φret v) ∨
      (∃ f ls f_body f_body' params retty,
         ⌜ eh = Ecall f (map (λ l : addr, Evalue (Vptr l)) ls) ∧
           instantiate_f_body (add_params_to_env (Env [] []) params ls) f_body = Some f_body' ⌝ ∗
         text_interp f (Function retty params f_body) ∗
         (▷ wpr E f_body' (λ _, False)%I (λ v, wpr E (fill_ectxs (Evalue v) K) Φ Φret))))
  ))%I.

  Local Instance wpr_pre_contractive : Contractive wpr_pre.
  Admitted. (* XXX: We will first prove on paper instead *)

  Definition wpr_def:
    coPset → expr → (val → iProp Σ) → (val → iProp Σ) → iProp Σ := fixpoint wpr_pre.
  Definition wpr_aux : { x | x = @wpr_def }. by eexists. Qed.
  Definition wpr := proj1_sig wpr_aux.
  Definition wpr_eq : @wpr = @wpr_def := proj2_sig wpr_aux.

  Lemma wpr_unfold E e Φ Φret : wpr E e Φ Φret ⊣⊢ wpr_pre wpr E e Φ Φret.
  Proof. rewrite wpr_eq. apply (fixpoint_unfold wpr_pre). Qed.

  Lemma wpr_helper E P R Q e eh K:
    unfill_expr e [] = Some (K, eh) →
    (∀ v, P v -∗ R -∗ Q v) ∗
    ▷ R ∗
    WP eh @ E {{ P }}
    ⊢ WP eh @ E {{ Q }}.
  Proof.
    iIntros (?) "[? [HR ?]]".
    assert (to_val eh = None) as ?.
    { move : (cont_uninj' _ _ _ H0) => [? ?].
      by apply enf_not_val. }
    iDestruct (wp_frame_step_l' with "[-~]") as "?"=>//.
    { iFrame "HR". iFrame. }
    iApply (wp_strong_mono E E)=>//.
    iFrame. iIntros (?) "[? ?]".
    iModIntro. iApply ("~" with "[-~1]")=>//.
  Qed.

  Lemma wpr_step_mono E eh (Φ1 Φ2: val → iProp Σ):
    (□ (∀ v, Φ1 v -∗ Φ2 v) ∗ (wpr E eh (λ _ : val, False) Φ1)%I ⊢ wpr E eh (λ _ : val, False) Φ2).
  Proof.
    iLöb as "IH" forall (Φ1 Φ2 eh). rewrite !wpr_unfold /wpr_pre.
    iIntros "[#? ?]". iDestruct "~1" as "[H | H]".
    - iDestruct "H" as (?) "[? ?]". eauto.
    - iDestruct "H" as (??) "[% [[% H] | [H | H]]]"; destruct H2.
      + iRight. iExists _, _.
        iSplit=>//. iLeft. iSplitL ""=>//.
        iApply (wpr_helper)=>//. iFrame "IH". iFrame.
        iIntros (?) "? ?".
        iApply "~2". iFrame. done.
      + iRight. iExists _, _.
        iSplit=>//. iRight. iLeft. iDestruct "H" as (?) "[% ?]".
        iExists _. iSplit=>//. iNext. by iApply "~".
      + iRight. iExists _, _.
        iSplit=>//. iRight. iRight. iDestruct "H" as (??????) "[% [? ?]]".
        destruct H10. iExists _, _, _, _, _, _.
        iSplit=>//. iFrame. iNext. iApply "IH". iFrame.
        iAlways. iIntros (?) "?".
        iApply "IH". iFrame.
        done.
  Qed.

  Lemma wpr_value E v Φ Φret:
    Φ v ⊢ wpr E (Evalue v) Φ Φret.
  Proof.
    rewrite wpr_unfold /wpr_pre. iIntros "?".
    iLeft. eauto.
  Qed.

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
          iApply wpr_helper=>//.
          iFrame "IH". iFrame.
          iIntros (?) "? ?".
          rewrite -fill_app. iApply "~1". done.
      + iDestruct "~" as (v) "[% ?]". iRight. iExists eh, (kes ++ K). iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iRight. iLeft. iExists v. by iSplitL "".
      + iDestruct "~" as (??????) "[% [? ?]]". destruct H8.
        iRight. iExists eh, (kes ++ K). iSplit.
        * iPureIntro. split.
          { by apply fill_ectxs_not_val. }
          { by apply unfill_app. }
        * iRight. iRight. iExists _, _, _, _, _, _.
          iSplitL ""; first done.
          iFrame. iApply wpr_step_mono.
          iFrame. iNext. iAlways.
          iIntros (?) "?".
          rewrite -fill_app. iApply "IH".
          done.
  Qed.

  Lemma wpr_ret v E Φ Φret:
    Φret v ⊢ wpr E (Erete (Evalue v)) Φ Φret.
  Proof.
    iIntros "H".
    rewrite wpr_unfold /wpr_pre.
    iRight. iExists (Erete (Evalue v)), [].
    iSplit.
    - iPureIntro. split=>//.
    - iRight. iLeft. iExists v. iSplitL ""=>//. eauto.
  Qed.

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
    iRight. iRight. iExists _, _, _, _, _, _. iFrame.
    iSplitL "".
    { iPureIntro. split=>//. by subst. }
    iNext. iApply wpr_step_mono. iFrame.
    iAlways. iIntros (?). iApply wpr_value.
  Qed.

  Lemma stack_agree_s s σ:
    stack_interp s ∗ state_interp σ ⊢ ⌜ s_stack σ = s⌝.
  Proof.
    iIntros "(?&(?&?&?))".
    iDestruct (stack_agree with "[~ ~3]") as "%"; first iFrame.
    done.
  Qed.

  Lemma lookup_text_s f x σ:
    text_interp f x ∗ state_interp σ ⊢ ⌜s_text σ !! f = Some x⌝.
  Proof.
    iIntros "(?&(?&?&?))".
    iDestruct (lookup_text with "[~ ~2]") as "%"; first iFrame.
    done.
  Qed.

  Lemma wp_call_r E ks es ls params f_body f_body' f retty k Φ:
    es = map (fun l => Evalue (Vptr l)) ls →
    instantiate_f_body (add_params_to_env (Env [] []) params ls) f_body = Some f_body' →
    text_interp f (Function retty params f_body) ∗ stack_interp ks ∗
    ▷ wpr E f_body' (fun _ => False%I) (λ v, stack_interp ks -∗ WP (fill_ectxs (Evalue v) k) @ E {{ Φ }})
    ⊢ wp E (fill_ectxs (Ecall f es) k) Φ.
  Proof.
    iIntros (??) "(?&?&?)".
    iApply (@wp_call _ _ _ k)=>//.
    iFrame. iNext. iIntros "H". clear H1.
    iLöb as "IH" forall (Φ k ks f_body').
    rewrite wp_unfold /wp_pre.
    rewrite wpr_unfold /wpr_pre.
    iDestruct "~2" as "[H' | H']".
    - by iDestruct "H'" as (?) "[_ %]".
    - iDestruct "H'" as (??) "[% [[% ?] | [? | ?]]]".
      + iRight. destruct H3.
        iSplit=>//.
        iIntros (?) "Hσ1".
        move: (cont_uninj' _ _ _ H5) => [Ha Hb]. subst.
        clear H5.
        rewrite wp_unfold /wp_pre.
        iDestruct "~1" as "[?|?]".
        * iDestruct "~1" as (?) "[% _]". apply enf_not_val in Ha.
          simpl in H5. rewrite Ha in H5. done.
        * iDestruct "~1" as "[% ?]".
          iSpecialize ("~" $! a with "Hσ1").
          iMod "~" as "[% ?]".
          iModIntro. iSplit.
          { iPureIntro. inversion H5 as (e'&σ'&?&?).
            eexists _, σ', []. constructor=>//.
            destruct a. destruct σ'.
            simpl in H6. destruct H6. move:(enf_not_val _ Ha)=>Hn.
            move: (not_jmp_preserves [] _ _ _ _ Hn H4 c) => /= [? [? ?]]. subst.
            apply CSestep. apply ESbind=>//. }
          iNext. iIntros (e2 σ2 efs) "%".
          simpl in H6. destruct H6. move:(enf_not_val _ Ha)=>Hn.
          move: (not_jmp_preserves _ _ _ _ _ Hn H4 H6) => /= [Heqs [Heqt H']].
          apply fill_estep_inv in H'=>//.
          destruct H' as [? [? ?]]. subst.
          iSpecialize ("~1" $! x σ2 []).
          iAssert (⌜step H1 a x σ2 []⌝)%I as "?".
          { iPureIntro. split=>//.
            destruct a. destruct σ2.
            simpl in Heqs, Heqt. subst.
            constructor. simpl in H8. done. }
          iMod ("~1" with "~") as "[? [? ?]]". iModIntro.
          iFrame. iApply wp_bind=>//.
          { eapply estep_preserves_not_jmp=>//. }
            iApply (wp_strong_mono E E)=>//.
          iFrame. iIntros (?) "H'".
          iModIntro. iApply ("IH" with "[-H]")=>//.
      +  destruct H3.
         iDestruct "~" as (?) "[% ?]". subst.
         apply cont_uninj' in H4. destruct H4. subst.
         iRight.
         iSplit=>//.
         iIntros (σ1) "Hσ1".
         iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
         iModIntro.
         iDestruct (stack_agree_s with "[H Hσ1]") as "%"; first iFrame.
         iSplit.
         { iPureIntro. destruct σ1. simpl in H1.
           eexists _, (State s_heap s_text ks), []. split; [|split]=>//.
           apply CSjstep. subst. apply JSrete.
           by apply cont_uninj. }
         iNext; iIntros (e2 σ2 efs ?).
         simpl in H4. destruct H4.
         inversion H4; subst.
         { by apply fill_estep_false in H7. }
         inversion H7; subst.
         * apply cont_inj in H6=>//. destruct H6. inversion H6. subst.
           iDestruct "Hσ1" as "(?&?&?)".
           iMod (stack_pop with "[H ~2]") as "(Hstk & Hs & %)"; first iFrame.
           destruct H8; subst.
           iFrame. iMod "Hclose" as "_".
           iModIntro. iSplitL.
           { simpl. by iApply "~1". }
           by rewrite big_sepL_nil.
         * apply cont_inj in H6=>//.
           destruct H6 as [? ?]; done.
      + destruct H3.
        iDestruct "~" as (??????) "[% [? ?]]".
        destruct H11.
        apply cont_uninj' in H4. destruct H4. subst.
        iRight. iSplit=>//.
        iIntros (σ1) "Hσ1".
        iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
        iModIntro.
        iDestruct (stack_agree_s with "[H Hσ1]") as "%"; first iFrame.
        iDestruct (lookup_text_s with "[~1 Hσ1]") as "%"; first iFrame.
        iSplit.
        { iPureIntro. destruct σ1. simpl in H0. subst.
          eexists _, (State s_heap s_text (H2::k::ks)), []. split; [|split]=>//.
          constructor. eapply JScall=>//. }
        iNext; iIntros (e2 σ2 efs ?).
        simpl in H11. destruct H11.
         inversion H11; subst.
         { by apply fill_estep_false in H14. }
         inversion H14; subst.
         * apply cont_inj in H13=>//. destruct H13. inversion H13.
         * apply cont_inj in H13=>//. destruct H13. inversion H13. subst.
           apply map_inj in H20. subst.
           simpl in H0. subst.
           iDestruct "Hσ1" as "(?&?&?)".
           iMod (stack_push with "[~3 H]") as "(Hs & Hstk & %)"; first iFrame.
           iFrame.
           iMod "Hclose" as "_".
           iModIntro. iSplitL.
           simpl in H1. rewrite H1 in H16.
           inversion H16. subst. clear H16. clear H1.
           rewrite H18 in H12. inversion H12. subst. clear H13.
           iApply ("IH" $! _ H2 (k::ks) with "[-Hs]")=>//.
           iApply wpr_step_mono. iFrame.
           iClear "~1". iAlways.
           iIntros (?) "? ?".
           (* iSpecialize ("IH" $! Φ k (fill_ectxs (Evalue ) H2) with "~"). *)
           iApply ("IH" with "[-~1]")=>//.
           by rewrite big_sepL_nil.
           { intros. by inversion H15. }
  Qed.

  Lemma wpr_op E op v1 v2 v' Φ Φret:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ wpr E (Ebinop op (Evalue v1) (Evalue v2)) Φ Φret.
  Proof.
    iIntros (?) "?".
    rewrite wpr_unfold /wpr_pre.
    iRight. iExists _, _.
    iSplit=>//.
    iLeft. iSplitL ""=>//.
    iApply wp_op=>//.
    by iApply wpr_value.
  Qed.

End wp_ret.
