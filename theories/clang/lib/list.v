(* Singly linked list *)

From iris.base_logic.lib Require Export wsat.
From iris_c.clang Require Import logic tactics notations.
Require Import lib.gmap_solve.

Section proof.
  Context `{clangG Σ}.

  (* de brujin with autosubst? *)
  Definition tcell (t: type): type := Tprod t (Tptr Tvoid).

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
    - iIntros "%". iPureIntro. by subst.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      destruct H2 as (?&?&?). by subst.
  Qed.

  Lemma isList_ptr' (l: val) (xs: list val) (t: type) :
    isList l xs t ⊢ ⌜ typeof l (Tptr (tcell t)) ⌝.
  Proof.
    destruct xs as [|x xs'].
    - iIntros "%". iPureIntro. by subst.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      destruct H2 as (?&?&?). by subst.
  Qed.

  Definition x: ident := 1.
  Definition y: ident := 2.
  Definition t: ident := 3.

  Notation "'Tlist'" := (Tptr (tcell Tint32)).

  Definition rev_list : expr :=
    let: t ::: Tptr Tlist := Ealloc (Tptr Tlist) null in
    while [ x != null ] ( x != null ) <{
      t <- snd (!?x) ;;
      snd (!?x) <- y ;;
      y <- x ;;
      x <- t
    }>.

  Definition ps :=
    [ (x, Tlist); (y, Tptr Tvoid) ].

  Lemma rev_spec' (f: ident) ks Φ px py pt xs:
    ∀ lx ly ys,
      isList lx xs Tint32 ∗
      isList ly ys Tint32 ∗
      (∀ ly' : val,
          isList ly' (rev xs ++ ys) Tint32 -∗ own_stack ([] :: ks) -∗ Φ void) ∗
      own_stack ([] :: ks) ∗
      px ↦ lx @ Tlist ∗
      py ↦ ly @ Tptr Tvoid ∗
      pt ↦ - @ Tptr Tlist
  ⊢ WP while [! px @ Tlist != null](! px @ Tlist != null)<{
     pt <- snd ! ! px @ Tlist @ (tcell Tint32) ;;
     ! px @ Tlist + Byte.repr 4 <- ! py @ (Tptr Tvoid) ;;
     py <- ! px @ Tlist ;; px <- ! pt @ (Tptr Tlist) }> {{ v,
  Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs']; intros ??? ; subst.
    - iIntros "(Hlx & Hly & HΦ & Hs & Hpx & Hpy & Hpt)".
      iDestruct "Hlx" as "%". wp_run.
      { by simplify_eq. } wp_run. iNext.
      iApply ("HΦ" with "[-Hs]")=>//.
    - iIntros "(Hlx & Hly & HΦ & Hs & Hpx & Hpy & Hpt)".
      wp_load. iDestruct "Hlx" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      wp_run. iNext. wp_run. iNext.
      iDestruct "Hpt" as (?) "Hpt".
      wp_assign. wp_load. destruct p as [pb po]. wp_op.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval (Byte.repr 4))) with 4%nat; last done.
      replace (Z.to_nat (Byte.intval (Byte.repr 4))) with 4%nat; last done. wp_load.
      iDestruct (isList_ptr with "Hly") as "%". unfold tcell.
      iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
      wp_assign. wp_load. wp_assign. wp_load. wp_assign.
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      iFrame. iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp".
      { iSplitL "Hp1"; by simpl. }
      iSplitL "Hp Hly".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. split; [|split]=>//. by eapply typeof_any_ptr. }
      iSplitL "HΦ".
      { by rewrite -app_assoc. } eauto.
  Qed.

  Lemma rev_spec (f: ident) ks Φ xs:
    ∀ lx ly ys,
      text_interp f (Function Tvoid ps rev_list) ∗
      isList lx xs Tint32 ∗ isList ly ys Tint32 ∗ own_stack ks ∗
      (∀ ly', isList ly' (rev xs ++ ys) Tint32 -∗ own_stack ([]::ks) -∗ Φ Vvoid)
      ⊢ WP Ecall_typed Tvoid f [Evalue lx ; Evalue ly] {{ Φ }}.
  Proof.
    iIntros (???) "(Hf & Hlx & Hly & Hs & HΦ)". unfold rev_list.
    iApply (@wp_call _ _ _ [] _ [lx; ly]); last iFrame; first by simpl.
    iNext. iIntros "Hs'".
    wp_bind (Ealloc _ _).
    iDestruct (isList_ptr with "Hly") as "%".
    iDestruct (isList_ptr' with "Hlx") as "%".
    iApply wp_alloc=>//. iIntros (px) "Hpx".
    iApply wp_let=>//.
    iNext. wp_bind (Ealloc _ _).
    iApply wp_alloc=>//. iIntros (py) "Hpy".
    iApply wp_let=>//.
    iNext.  wp_bind (Ealloc _ _).
    iApply wp_alloc=>//. iIntros (pt) "Hpt".
    iApply wp_let=>//.
    iNext.
    iApply (rev_spec' f ks Φ px py pt xs lx ly ys). iFrame. eauto.
  Qed.

End proof.

