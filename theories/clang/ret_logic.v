From iris_c.clang Require Export logic.
From iris_c.lib Require Import pair.

Axiom cont_uninj':
  ∀ e eh K, unfill_expr e [] = Some (K, eh) → enf eh ∧ e = fill_ectxs eh K.

Arguments cont_uninj' {_ _ _} _.

Axiom cont_uninj:
  ∀ kes e, enf e → unfill_expr (fill_ectxs e kes) [] = Some (kes, e).

Lemma unfill_app e eh K K':
  unfill_expr e [] = Some (K, eh) →
  unfill_expr (fill_ectxs e K') [] = Some (K' ++ K, eh).
Proof.
  intros H. move: (cont_uninj' H) => [? ?].
  subst. rewrite fill_app. by apply cont_uninj.
Qed.

Section wp_ret.
  Context `{clangG Σ}.

  Definition wpr_pre
    (wpr : coPset -c> expr -c> (val -c> iProp Σ) -c> (val -c> iProp Σ) -c> iProp Σ) :
    coPset -c> expr -c> (val -c> iProp Σ) -c> (val -c> iProp Σ) -c> iProp Σ := λ E e1 Φ Φret, (
  (* value case *)
  (∃ v, ⌜to_val e1 = Some v⌝ ∧ Φ v) ∨
  (* local case *)
  (⌜to_val e1 = None ⌝ ∧ ∃ eh K,
     ⌜ unfill_expr e1 [] = Some (K, eh) ⌝ ∧
     ((∀ ks, ⌜ is_jmp eh = false ⌝ ∗ WP (eh, ks) @ E {{ v, wpr E (fill_ectxs (Evalue v) K) Φ Φret }}) ∨
      (∃ v, ⌜ eh = Erete (Evalue v) ⌝ ∗ ▷ Φret v) ∨
      (∃ f vs e e' params retty,
         ⌜ eh = Ecall retty f (map Evalue vs) ∧
           let_params vs params e = Some e' ⌝ ∗
         f T↦ Function retty params e ∗
         (▷ wpr E e' (λ _, False)%I (λ v, wpr E (fill_ectxs (Evalue v) K) Φ Φret))))
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

  Lemma wpr_helper E P R Q e eh K ks:
    unfill_expr e [] = Some (K, eh) →
    (∀ v, P v -∗ R -∗ Q v) ∗
    ▷ R ∗
    WP (eh, ks) @ E {{ P }}
    ⊢ WP (eh, ks) @ E {{ Q }}.
  Proof.
    iIntros (?) "[? [HR ?]]".
    assert (to_val eh = None) as ?.
    { move : (cont_uninj' H0) => [? ?].
      by apply enf_not_val. }
    iDestruct (wp_frame_step_l' _ (eh : language.expr clang_lang, ks) with "[-~]") as "?"=>//.
    { iFrame "HR". iFrame. }
    iApply (wp_strong_mono E E)=>//.
    iFrame. iIntros (?) "[? ?]".
    iModIntro. iApply ("~" with "[-~1]")=>//.
  Qed.

  Lemma wpr_step_mono E eh (Φ1 Φ2: val → iProp Σ):
    (□ (∀ v, Φ1 v -∗ Φ2 v) ∗ (wpr E eh (λ _ : val, False) Φ1)%I ⊢ wpr E eh (λ _ : val, False) Φ2).
  Proof.
    iLöb as "IH" forall (Φ1 Φ2 eh). rewrite !wpr_unfold /wpr_pre.
    iIntros "[#H12 [H | [% H]]]".
    - iDestruct "H" as (?) "[? ?]". eauto.
    - iDestruct "H" as (??) "[% [H | [H | H]]]".
      + iRight. iSplit=>//. iExists _, _.
        iSplit=>//. iLeft.
        iIntros (ks). iDestruct ("H" $! ks) as "[% H]".
        iSplitL ""=>//.
        iApply wpr_helper=>//. iFrame "IH". iFrame.
        iIntros (?) "H1 H2".
        iApply "H2". by iFrame.
      + iRight. iSplit=>//. iExists _, _.
        iSplit=>//. iRight. iLeft. iDestruct "H" as (?) "[% H]".
        iExists _. iSplit=>//. iNext. by iApply "H12".
      + iRight. iSplit=>//. iExists _, _.
        iSplit=>//. iRight. iRight. iDestruct "H" as (??????) "[% [? ?]]".
        destruct H10. iExists _, _, _, _, _, _.
        iSplit=>//. iFrame. iNext. iApply "IH". iFrame.
        iAlways. iIntros (?) "?".
        iApply "IH". by iFrame.
  Qed.

  Lemma wpr_value E v Φ Φret:
    Φ v ⊢ wpr E (Evalue v) Φ Φret.
  Proof. rewrite wpr_unfold /wpr_pre. iIntros "?". iLeft. eauto. Qed.

  Lemma wpr_bind kes E e Φ Φret :
    wpr E e (fun v => wpr E (fill_ectxs (Evalue v) kes) Φ Φret) Φret
    ⊢ wpr E (fill_ectxs e kes) Φ Φret.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ Φret). rewrite !wpr_unfold /wp_pre.
    iDestruct "H" as "[H | [% H]]".
    - iDestruct "H" as (v) "[% ?]".
      apply of_to_val in H0. subst.
      by rewrite wpr_unfold /wpr_pre.
    - iDestruct "H" as (eh K) "(% & [ H | [H | H]])".
      + iRight. iSplit=>//; first by iPureIntro; apply fill_ectxs_not_val.
        iExists eh, (kes ++ K).
        iSplit; first by iPureIntro; apply unfill_app.
        iLeft. iIntros (ks). iDestruct ("H" $! ks) as "[% H]". iSplitL ""; first done.
        iApply wpr_helper=>//.
        iFrame "IH". iFrame.
        iIntros (?) "H1 H2".
        rewrite -fill_app. by iApply "H2".
      + iDestruct "H" as (v) "[% H]". iRight.
        iSplit=>//; first by iPureIntro; apply fill_ectxs_not_val.
        iExists eh, (kes ++ K).
        iSplit; first by iPureIntro; apply unfill_app.
        iRight. iLeft. iExists v. by iSplitL "".
      + iDestruct "H" as (??????) "[% [? ?]]". destruct_ands.
        iRight.
        iSplit=>//; first by iPureIntro; apply fill_ectxs_not_val.
        iExists _, (kes ++ K).
        iSplit; first by iPureIntro; apply unfill_app.
        iRight. iRight. iExists _, _, _, _, _, _.
        iSplitL ""=>//.
        iFrame. iApply wpr_step_mono.
        iFrame. iNext. iAlways.
        iIntros (?) "?". rewrite -fill_app. by iApply "IH".
  Qed.

  Lemma wpr_seq E e1 e2 Φ Φret:
    wpr E e1 (λ v, wpr E (Eseq (Evalue v) e2) Φ Φret) Φret ⊢ wpr E (Eseq e1 e2) Φ Φret.
  Proof. iIntros "Hseq". iApply (wpr_bind [EKseq e2])=>//. Qed.

  Lemma wpr_ret v E Φ Φret:
    Φret v ⊢ wpr E (Erete (Evalue v)) Φ Φret.
  Proof.
    iIntros "H".
    rewrite wpr_unfold /wpr_pre.
    iRight. iSplit=>//. iExists (Erete (Evalue v)), [].
    iSplit.
    - iPureIntro. split=>//.
    - iRight. iLeft. iExists v. iSplitL ""=>//. eauto.
  Qed.

  Lemma wpr_call E vs params e e' f retty Φ Φret:
    let_params vs params e = Some e' →
    f T↦ Function retty params e ∗
    ▷ wpr E e' (fun _ => False%I) Φ
    ⊢ wpr E (Ecall retty f (map Evalue vs)) Φ Φret.
  Proof.
    iIntros (?) "[? ?]".
    iApply wpr_unfold. rewrite /wpr_pre.
    iRight.
    iSplit.
    { iPureIntro. split=>//. }
    iExists (Ecall retty f _), [].
    iSplit.
    { iPureIntro. simpl. by rewrite forall_is_val. }
    iRight. iRight. iExists _, _, _, _, _, _. iFrame.
    iSplitL "".
    { iPureIntro. split=>//. }
    iNext. iApply wpr_step_mono. iFrame.
    iAlways. iIntros (?). iApply wpr_value.
  Qed.

  Lemma lookup_text_s f x σ:
    f T↦ x ∗ state_interp σ ⊢ ⌜s_text σ !! f = Some x⌝.
  Proof.
    iIntros "(?&(?&?))".
    by iDestruct (lookup_text with "[~ ~2]") as "%"; first iFrame.
  Qed.

  Tactic Notation "cont_uninj'" :=
    match goal with
      | [ H : unfill_expr _ _ = Some _ |- _ ] =>
        let H' := fresh "H'" in
        move: (cont_uninj' H) => H'; clear H; destruct_ands
    end.

  Tactic Notation "enf_not_val" :=
    match goal with
      | [ H: enf _ |- _ ] =>
        let H' := fresh "H'" in
        move:(enf_not_val _ H)=>H'
    end.

  Tactic Notation "not_jmp_preserves" ident(Hes) :=
    match goal with
      | [ Hjn: is_jmp ?E = false , Hn: to_val ?E = None, Hc: cstep ?E _ _ _ _ _ _ |- _ ] =>
        move: (not_jmp_preserves [] _ _ _ _ _ _ _ Hn Hjn Hc) => /= [? [? Hes]]
      | [ Hjn: is_jmp ?E = false , Hn: to_val ?E = None, Hc: cstep (fill_ectxs ?E ?K) _ _ _ _ _ _ |- _ ] =>
        move: (not_jmp_preserves _ _ _ _ _ _ _ _ Hn Hjn Hc) => /= [? [? Hes]]
    end; subst.

  Lemma wp_call_r E ks vs params e e' f retty k Φ:
    let_params vs params e = Some e' →
    f T↦ Function retty params e ∗
    ▷ wpr E e' (fun _ => False%I) (λ v, WP (fill_ectxs (Evalue v) k, ks) @ E {{ Φ }})
    ⊢ WP (fill_ectxs (Ecall retty f (map Evalue vs)) k, ks) @ E {{ Φ }}.
  Proof.
    iIntros (?) "(?&?)".
    iApply (wp_call k)=>//.
    iFrame. iNext. clear H0.
    iLöb as "IH" forall (Φ k ks e').
    rewrite wp_unfold /wp_pre.
    rewrite wpr_unfold /wpr_pre.
    iDestruct "~1" as "[H' | [% H']]".
    - by iDestruct "H'" as (?) "[_ %]".
    - iDestruct "H'" as (??) "[% [H' | [H' | H']]]".
      + iRight. destruct_ands. iSplit=>//.
        iIntros (σ1) "Hσ1".
        cont_uninj'. iDestruct ("H'" $! (Kcall k::ks)) as "[% H']".
        rewrite wp_unfold /wp_pre.
        iDestruct "H'" as "[H'|H']".
        * iDestruct "H'" as (?) "[% _]".
          enf_not_val. simpl in *. simplify_eq.
        * iDestruct "H'" as "[% H']".
          iMod ("H'" $! σ1 with "Hσ1") as "[% H']"; first iFrame.
          iModIntro. iSplit.
          { iPureIntro. inversion H6 as (e'&?&σ'&?&Hcs). simpl in *.
            eexists _, _, σ', _. simpl in *. not_jmp_preserves Hes.
            destruct σ1. destruct σ'.
            simpl in *. enf_not_val. subst.
            apply CSestep. apply ESbind=>//. }
          iNext. iIntros (e2 σ2 efs) "%".
          simpl in *. enf_not_val.
          not_jmp_preserves Hes.
          apply fill_estep_inv in Hes=>//.
          destruct Hes as [? [? ?]]. destruct e2. simpl in *. subst.
          iSpecialize ("H'" $! (x, Kcall k::ks) σ2 efs). simpl.
          iAssert (⌜cstep H1 (Kcall k::ks) σ1 x (Kcall k::ks) σ2 efs⌝)%I as "Hs".
          { iPureIntro. destruct σ1. destruct σ2.
            simpl in *. subst. constructor. done. }
          iMod ("H'" with "Hs") as "[? [? ?]]". iModIntro.
          iFrame. iApply wp_bind=>//.
          { eapply estep_preserves_not_jmp=>//. }
            iApply (wp_strong_mono E E)=>//.
          iFrame. iIntros (?) "H'".
          iModIntro. iApply ("IH" with "[-]")=>//.
      +  destruct_ands.
         iDestruct "H'" as (?) "[% H']". subst.
         cont_uninj'. iRight.
         iSplit=>//.
         iIntros (σ1) "Hσ1".
         iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
         iModIntro.
         iSplit.
         { iPureIntro. destruct σ1. simpl in *.
           eexists _, ks, (State s_heap s_text), _. simpl.
           apply CSjstep. subst. apply JSrete with (KS := []). done. }
         iNext; iIntros (e2 σ2 efs Hs).
         simpl in *. inversion_cstep_as Hes Hjs Hws; subst.
         { by apply fill_estep_false in Hes. }
         inversion_jstep_as Heq; subst.
         * apply cont_inj in Heq=>//; auto. destruct Heq as [Heq ?].
           inversion Heq. subst.
           iDestruct "Hσ1" as "(H1&H3)".
           iFrame. iMod "Hclose" as "_".
           iModIntro. iSplitL.
           { simpl. destruct e2. simpl in *. simplify_eq.
             apply kcall_map in H7=>//. destruct_ands.
             by iApply "H'". }
           by rewrite big_sepL_nil.
         * apply cont_inj in Heq=>//; auto. by destruct_ands.
         * apply fill_wstep_false in Hws=>//.
      + destruct_ands.
        iDestruct "H'" as (??????) "[% [H1 H2]]".
        destruct_ands. cont_uninj'.
        iRight. iSplit=>//.
        iIntros (σ1) "Hσ1".
        iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
        iModIntro.
        iDestruct (lookup_text_s with "[H1 Hσ1]") as "%"; first iFrame.
        iSplit.
        { iPureIntro. destruct σ1. simpl in *. subst.
          eexists _, (_::Kcall k::ks), (State s_heap s_text), [].
          constructor. eapply JScall=>//. }
        iNext; iIntros (e2 σ2 efs Hcs). simpl in *.
        inversion_cstep_as Hes Hjs Hws.
         { by apply fill_estep_false in Hes. }
         { inversion_jstep_as Heq; subst.
           * fill_enf_neq.
           * apply cont_inj in Heq=>//; auto. destruct Heq as [Heq ?].
             inversion Heq. simplify_eq.
             apply map_inj in Heq; last by inversion 1.
             simpl in *. subst. simplify_eq.
             iDestruct "Hσ1" as "(?&?)".
             iFrame. iMod "Hclose" as "_".
             iModIntro. iSplitL; last by rewrite big_sepL_nil.
             destruct e2. simpl in *. simplify_eq.
             iApply ("IH" $! _ _ (Kcall k::ks) with "[-]")=>//.
             iApply wpr_step_mono. iFrame.
             iClear "H1". iAlways.
             iIntros (?) "H1".
             iApply ("IH" with "[-]")=>//. }
         { apply fill_wstep_false in Hws=>//. }
  Qed.

  Lemma wpr_head E eh Φ Φret:
    is_jmp eh = false → enf eh → (∀ ks, WP (eh, ks) @ E {{ Φ }}) ⊢ wpr E eh Φ Φret.
  Proof.
    iIntros (??) "?".
    rewrite wpr_unfold /wpr_pre.
    iRight. iSplit=>//.
    { iPureIntro. by apply enf_not_val. }
    iExists eh, []. iSplit=>//.
    { iPureIntro. by eapply (cont_uninj []). }
    iLeft. iIntros (ks). iDestruct ("~" $! ks) as "?". iSplitL ""=>//.
    iApply (wp_strong_mono E E)=>//. iFrame.
    iIntros (?) "HΦ".
    by iApply wpr_value.
  Qed.

  Lemma wpr_op E op v1 v2 v' Φ Φret:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ wpr E (Ebinop op (Evalue v1) (Evalue v2)) Φ Φret.
  Proof. iIntros (?) "?". iApply wpr_head=>//; auto. iIntros (?). iApply wp_op=>//. Qed.

End wp_ret.
