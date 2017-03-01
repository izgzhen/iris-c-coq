(* Singly linked list *)

From iris_os.clang Require Import logic tactics notations.
Require Import lib.gmap_solve.

Section proof.
  Context `{clangG Σ}.

  (* de brujin with autosubst? *)
  Definition tcell (telem: type): type := Tprod telem (Tptr Tvoid).
  Definition tlist (telem: type): type := Tptr (tcell telem).

  Fixpoint isList (l: val) (xs: list val) (t: type) :=
    match xs with
      | [] => (⌜ l = null ⌝)%I
      | x::xs' => (∃ p l',
                     ⌜ l = Vptr p ∧ typeof x t ∧ typeof l' (tlist t) ⌝ ∗
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
  Parameter x: ident.

  Definition rev_list (telem: type) : stmts :=
    while [ x != null ] ( x != null ) <{
      pt <- snd (!x) ;;
      snd (!x) <- !py ;;
      py <- x ;;
      x <- !pt
    }>.

  Lemma rev_spec Φ Φret body xs:
    ∀ lx ly ys,
    instantiate_f_body {[ x := (tlist Tint32, px) ]} (rev_list Tint32) = Some body →
    isList lx xs Tint32 ∗ isList ly ys Tint32 ∗ pt ↦ - @ Tptr Tvoid ∗
    px ↦ lx @ tlist Tint32 ∗ py ↦ ly @ tlist Tint32 ∗
    (∀ ly', py ↦ ly' @ tlist Tint32 ∗ isList ly' (rev xs ++ ys) Tint32 -∗ Φ Vvoid)
    ⊢ WP curs body {{ Φ; Φret }}.
  Proof.
    induction xs as [|x xs' IHxs'];
    unfold_f_inst;
    destruct (decide (x = x))=>//;
    intros ??? [=]; destruct px; subst.
    - iIntros "(% & Hlr & Ht & Hpx & Hpy & HΦ)".
      subst. wp_load. wp_op.
      iApply wp_while_false.
      iNext. iApply "HΦ". iFrame.
    - iIntros "(Hl & Hlr & Ht & Hpx & Hpy & HΦ)".
      destruct (decide (proof.x = proof.x))=>//.
      wp_load. iDestruct "Hl" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      wp_op. iApply wp_while_true.
      iNext. repeat (iApply wp_seq).
      iApply (wp_bind [EKderef; EKsnd] (SKassignl _)). (* TODO: Some bug in tactic *)
      iApply wp_load. iFrame. iIntros "!> Hbo".
      simpl. wp_load. wp_bind (Esnd _).
      iApply wp_snd. iNext. iApply wp_value=>//.
      iDestruct "Ht" as (?) "Ht".
      wp_run.
      iApply (wp_bind [EKbinopr _ _] (SKassignr _)).
      iApply wp_load. iFrame. iIntros "!> ?".
      simpl. iApply (wp_bind [] (SKassignr _)).
      destruct p as [pb po].
      iApply wp_op=>//. simpl.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval (Byte.repr 4))) with 4%nat; last done.
      wp_load. iDestruct (isList_ptr with "Hlr") as "%". wp_run=>//.
      unfold tlist. (* XXX: automatically unfold into Tptr? *) wp_assign.
      wp_load. wp_assign.
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      { unfold_f_inst. destruct (decide (proof.x = proof.x))=>//. }
      iFrame.
      iSplitL "Hp Hlr".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. repeat (split; first done). by eapply typeof_any_ptr. }
      iSplitL "Ht"; first eauto.
      replace (rev xs' ++ x :: ys) with ((rev xs' ++ [x]) ++ ys); first done; last by rewrite -app_assoc.
  Qed.
  
End proof.
