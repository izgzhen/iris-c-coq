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
                     ⌜ l = Vptr p ∧ typeof t x ∧ typeof (tlist t) l' ⌝ ∗
                     p ↦ Vpair x l' ∗ isList l' xs' t)%I
    end.

  Lemma isList_ptr (l: val) (xs: list val) (t: type) :
    isList l xs t ⊢ ⌜ typeof (Tptr Tvoid) l ⌝.
  Proof.
    destruct xs as [|x xs'].
    - iIntros "%". iPureIntro. subst. solve_typeof.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      destruct H2 as (?&?&?). subst. iPureIntro. solve_typeof.
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
    isList lx xs Tint32 ∗ isList ly ys Tint32 ∗ (∃ v: addr, pt ↦ v) ∗
    px ↦ lx ∗ py ↦ ly ∗
    (∀ ly', py ↦ ly' ∗ isList ly' (rev xs ++ ys) Tint32 -∗ Φ Vvoid)
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
      iApply (@wp_assign _ _ _ _ H0 l').
      { admit. } iFrame. iIntros "!> Ht".
      repeat (iApply wp_seq).
      iApply (wp_bind [EKbinopr _ _] (SKassignr _)).
      iApply wp_load. iFrame. iIntros "!> ?".
      simpl. iApply (wp_bind [] (SKassignr _)).
      destruct p as [pb po].
      iApply wp_op=>//. simpl.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval (Byte.repr 4))) with 4%nat; last done.
      wp_load. iDestruct (isList_ptr with "Hlr") as "%".
      iApply (@wp_assign_offset _ _ _ _ _ _ x l' ly)=>//.
      { admit. } { admit. }
      iFrame. iIntros "!> ?".
      wp_load. iApply (@wp_assign _ _ _ _ ly (Vptr (pb, po))).
      { admit. }
      iFrame. iIntros "!> ?".
      wp_load. iApply (@wp_assign _ _ _ _ (Vptr (pb, po)) l')=>//.
      { admit. }
      iFrame. iIntros "!> ?".
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      { unfold_f_inst. destruct (decide (proof.x = proof.x))=>//. }
      iFrame. simpl.
      iSplitL "~1 Hlr".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. repeat (split; first done).
        by eapply typeof_any_ptr. }
      iSplitL "Ht"; first admit.
      replace (rev xs' ++ x :: ys) with ((rev xs' ++ [x]) ++ ys); first done; last by rewrite -app_assoc.
  Admitted.
  
End proof.
