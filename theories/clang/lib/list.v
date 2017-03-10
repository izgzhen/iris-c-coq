(* Singly linked list *)

From iris_os.clang Require Import logic tactics notations.
Require Import lib.gmap_solve.

Section proof.
  Context `{clangG Σ}.

  (* de brujin with autosubst? *)
  Definition tcell (telem: type): type := Tprod telem (Tptr Tvoid).
  (* Definition tlist (telem: type): type := Tptr (tcell telem). *)

  Fixpoint isList (l: val) (xs: list val) (t: type) :=
    match xs with
      | [] => (⌜ l = null ⌝)%I
      | x::xs' => (∃ p l',
                     ⌜ l = Vptr p ∧ typeof x t ∧ typeof l' (Tptr (tcell t)) ⌝ ∗
                     p ↦ Vpair x l' @ tcell t ∗ isList l' xs' t)%I
    end.

  Lemma isList_ptr (l: val) (xs: list val) (t: type) :
    isList l xs t ⊢ ⌜ typeof l (Tptr Tvoid) ⌝.
  Proof.
    destruct xs as [|x xs'].
    - iIntros "%". iPureIntro. subst. constructor.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      destruct H2 as (?&?&?). subst. iPureIntro. constructor.
  Qed.
  
  Parameter py pt px: addr.
  Definition x: ident := 1.
  Definition y: ident := 2.
  Definition t: ident := 3.

  Definition rev_list (telem: type) : expr :=
    while [ x != null ] ( x != null ) <{
      t <- snd (!?x) ;;
      snd (!?x) <- y ;;
      y <- x ;;
      x <- t
    }>.

  Definition ev : env :=
    Env [(x, (Tptr (tcell Tint32), px));
         (y, (Tptr Tvoid, py));
         (t, (Tptr (tcell Tint32), pt))]
        [].
  
  Lemma rev_spec Φ body xs:
    ∀ lx ly ys,
      instantiate_f_body ev (rev_list Tint32) = Some body →
      isList lx xs Tint32 ∗ isList ly ys Tint32 ∗ pt ↦ - @ Tptr (tcell Tint32) ∗
      px ↦ lx @ Tptr (tcell Tint32) ∗ py ↦ ly @ Tptr Tvoid ∗
      (∀ ly', py ↦ ly' @ Tptr Tvoid ∗ isList ly' (rev xs ++ ys) Tint32 -∗ Φ Vvoid)
      ⊢ WP body {{ Φ }}.
  Proof.
    unfold_f_inst; destruct px; subst;
    induction xs as [|x xs' IHxs']; intros ??? [=]; subst.
    - iIntros "(% & Hlr & Ht & Hpx & Hpy & HΦ)".
      subst. wp_load. wp_op.
      iApply wp_while_false.
      iNext. iApply "HΦ". iFrame.
    - iIntros "(Hl & Hlr & Ht & Hpx & Hpy & HΦ)".
      wp_load. iDestruct "Hl" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      wp_op. iApply wp_while_true.
      iNext. wp_load. wp_load. wp_bind (Esnd _). iApply wp_snd. iNext.
      iApply wp_value=>//.
      iDestruct "Ht" as (?) "Ht".
      wp_assign. wp_load.
      destruct p as [pb po]. wp_op.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval (Byte.repr 4))) with 4%nat; last done.
      wp_load. iDestruct (isList_ptr with "Hlr") as "%".
      unfold tcell.
      iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
      wp_assign. wp_load. wp_assign. wp_load. wp_assign.
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)); first by unfold_f_inst.
      iFrame.
      iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp".
      { iSplitL "Hp1"; by simpl. }
      iSplitL "Hp Hlr".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. repeat (split; first done). by eapply typeof_any_ptr. }
      iSplitL "Ht"; first eauto.
      by rewrite -app_assoc.
  Qed.
  
End proof.
