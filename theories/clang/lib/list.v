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
                     p ↦ Vpair x l' @ (Tprod t (Tptr t)) ∗ isList l' xs' t)%I
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
    isList lx xs Tint32 ∗ isList ly ys Tint32 ∗ (∃ v, pt ↦ v @ tlist Tint32) ∗
    px ↦ lx @ tlist Tint32 ∗ py ↦ ly @ tlist Tint32 ∗
    (∀ ly', py ↦ ly' @ tlist Tint32 ∗ isList ly' (rev xs ++ ys) Tint32 -∗ Φ Vvoid)
    ⊢ WP curs body {{ Φ; Φret }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - iIntros (????) "(% & Hlr & Ht & Hpx & Hpy & HΦ)".
      subst. rewrite /instantiate_f_body /resolve_rhs map_to_list_singleton in H0.
      simpl in H0.
      destruct (decide (x = x))=>//.
      destruct px. gmap_solve.
      wp_load. wp_op. simpl.
      iApply wp_while_false.
      iNext. iApply "HΦ". iFrame.
    - iIntros (????) "(Hl & Hlr & Ht & Hpx & Hpy & HΦ)".
      rewrite /instantiate_f_body /resolve_rhs map_to_list_singleton in H0.
      simpl in H0.
      destruct (decide (x = x))=>//.
      destruct px. gmap_solve.
      wp_load. iDestruct "Hl" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      wp_op. iApply wp_while_true.
      iNext. repeat (iApply wp_seq).
      iApply (wp_bind [EKderef; EKsnd] (SKassignl _)). (* TODO: Some bug in tactic *)
      iApply wp_load. iFrame. iIntros "!> Hbo".
      simpl. wp_load. wp_bind (Esnd _).
      iApply wp_snd. iNext. iApply wp_value.
      iDestruct "Ht" as (?) "Ht".
      wp_assign. repeat (iApply wp_seq).
      iApply (wp_bind [EKbinopr _ _] (SKassignr _)).
      iApply wp_load. iFrame. iIntros "!> ?".
      simpl. iApply (wp_bind [] (SKassignr _)).
      destruct p as [pb po].
      iApply wp_op=>//. simpl.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval (Byte.repr 4))) with 4%nat; last done.
      wp_load. iDestruct (isList_ptr with "Hlr") as "%".
      iApply (wp_assign_offset Tint32)=>//.
      iFrame. iIntros "!> ?".
      wp_load. iApply (wp_assign (tlist Tint32)).
      apply typeof_ptr.
      iFrame. iIntros "!> ?".
      wp_load. iApply wp_assign=>//.
      iFrame. iIntros "!> ?".
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      { rewrite /instantiate_f_body /resolve_rhs map_to_list_singleton.
        simpl. destruct (decide (x = x))=>//.
        destruct px. gmap_solve. done. }
      iFrame. simpl.
      iSplitL "~1 Hlr".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. repeat (split; first done).
        by eapply typeof_any_ptr. }
      iSplitL "Ht"; first eauto.
      replace (rev xs' ++ x :: ys) with ((rev xs' ++ [x]) ++ ys); first done; last by rewrite -app_assoc.
  Qed.
  
End proof.
