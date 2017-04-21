(* Singly linked list *)

From iris.base_logic.lib Require Export wsat.
From iris_c.clang Require Import logic tactics notations.
From iris_c.lib Require Import gmap_solve int.

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

  Fixpoint isListSeg (l lt lt2: val) (x: val) (xs: list val) (t: type) :=
    match xs with
      | [] => (∃ p, ⌜ l = Vptr p ∧ l = lt ∧ typeof x t⌝ ∗ p ↦ Vpair x lt2 @ tcell t)%I
      | x'::xs' => (∃ p l',
                     ⌜ l = Vptr p ∧ typeof x t ∧ typeof l' (Tptr (tcell t)) ⌝ ∗
                     p ↦ Vpair x l' @ tcell t ∗ isListSeg l' lt lt2 x' xs' t)%I
    end.

  Lemma isList_ptr (l: val) (xs: list val) (t: type) :
    isList l xs t ⊢ ⌜ typeof l (Tptr Tvoid) ⌝.
  Proof.
    destruct xs as [|x xs'].
    - iIntros "%". iPureIntro. by subst.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      destruct_ands. by subst.
  Qed.

  Lemma isList_ptr' (l: val) (xs: list val) (t: type) :
    isList l xs t ⊢ ⌜ typeof l (Tptr (tcell t)) ⌝.
  Proof.
    destruct xs as [|x xs'].
    - iIntros "%". iPureIntro. by subst.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      destruct_ands. by subst.
  Qed.

  Definition x: ident := 1.
  Definition y: ident := 2.
  Definition t: ident := 3.
  Definition t': ident := 4.

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

  Definition traverse_list (lx: val) : expr :=
    while [ !lx@Tlist != null ] (!lx@Tlist != null) <{ lx <- snd (!(!lx@Tlist)@(tcell Tint32)) }>.

  Lemma traverse_spec Φ lx xs: ∀ l,
    lx ↦ l @ Tlist ∗ isList l xs Tint32 ∗ (isList l xs Tint32 -∗ Φ void)
    ⊢ WP traverse_list lx {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - iIntros (l) "[? [% HΦ]]".
      rewrite /traverse_list. subst.
      wp_run. by iApply "HΦ".
    - iIntros (l) "[Hlx [Hl HΦ]]".
      simpl. iDestruct "Hl" as (p l') "[% [Hp Hl']]".
      destruct_ands. subst.
      rewrite /traverse_list. wp_load. wp_op. iApply wp_while_true. iNext.
      wp_load. wp_load. wp_snd. iNext. wp_assign.
      iApply IHxs'. iFrame. iIntros "?".
      iApply "HΦ". iExists _, _. iFrame.
      done.
  Qed.

  Lemma lseg_snoc' v:
    typeof v Tint32 →
    ∀ xs x p p' (p'': addr) l'',
      typeof l'' Tlist →
      isListSeg p p' p'' x xs Tint32 ∗ p'' ↦ Vpair v l'' @ tcell Tint32
       ⊢ isListSeg p p'' l'' x (xs ++ [v]) Tint32.
  Proof.
    intros ?.
    induction xs as [|x' xs' IHxs']; iIntros (x p p' p'' l'' ?) "[Hl Hv]"; simpl.
    - iDestruct "Hl" as (p''') "[% ?]". destruct_ands. subst.
      iExists p''', p''. iSplit=>//. iFrame.
      iExists _. iFrame. done.
    - iDestruct "Hl" as (p''' l') "[% [? ?]]". destruct_ands. subst.
      specialize (IHxs' x' l' p' p'' l'').
      iDestruct (IHxs' with "[~1 Hv]") as "?"=>//; first iFrame.
      iExists _, _. iFrame. done.
  Qed.

  Lemma lseg_snoc v xs x p p' (p'': addr) l'':
    typeof v Tint32 → typeof l'' Tlist →
    isListSeg p p' p'' x xs Tint32 ∗ p'' ↦ Vpair v l'' @ tcell Tint32
    ⊢ isListSeg p p'' l'' x (xs ++ [v]) Tint32.
  Proof. iIntros (??) "?". iApply lseg_snoc'=>//. Qed.

  Lemma lseg_unsnoc: ∀ xs p (p': addr) x,
    isListSeg p p' null x xs Tint32 ⊢
    (∃ (x': val) xs' p'', isListSeg p p'' p' x xs' Tint32 ∗
     p' ↦ Vpair x' null @ tcell Tint32 ∗ ⌜ xs = xs' ++ [x'] ⌝ ) ∨
    (⌜ p = p' ∧ xs = [] ⌝ ∗ p' ↦ Vpair x null @ tcell Tint32).
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iIntros (???) "H". simpl. iDestruct "H" as (?) "[% ?]". destruct_ands. simplify_eq.
      iRight. by iFrame.
    - iIntros (???) "H". simpl. iDestruct "H" as (??) "[% [? ?]]". destruct_ands. simplify_eq.
      iDestruct (IHxs' with "~1") as "[?|[% ?]]".
      + iLeft. iDestruct "~2" as (???) "[? [? %]]". iExists H2. iFrame.
        subst. iExists (x'::H5). iExists _.
        iSplit=>//. simpl. iExists _, _.
        iFrame. done.
      + destruct_ands. subst. iLeft. iExists x'. iFrame.
        iExists [], H0. iSplit=>//. simpl. iExists _.
        iSplit=>//.
  Qed.

  Lemma lseg_to_list xs: ∀ p p' x,
    isListSeg p p' null x xs Tint32 ⊢ isList p (x::xs) Tint32.
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iDestruct 1 as (?) "[% ?]". destruct_ands. subst.
      iExists _, _. iFrame. iSplit=>//.
    - simpl. iDestruct 1 as (??) "[% [? ?]]". destruct_ands. subst.
      iDestruct (IHxs' with "~") as "?".
      iExists _, _. iFrame. iSplit=>//.
  Qed.

  Lemma enq_spec' lx (p: addr) Φ x xs: ∀ xs2 xs1 pt pt' (p': addr) l',
    typeof l' Tlist → typeof p Tlist →
    lx ↦ p @ Tlist ∗ pt ↦ p' @ Tlist ∗ pt' ↦ l' @ Tlist ∗
    isListSeg p p' l' x xs1 Tint32 ∗ isList l' xs2 Tint32 ∗ ⌜ xs = xs1 ++ xs2 ⌝ ∗
    (∀ p': addr, lx ↦ p @ Tlist -∗ pt ↦ p' @ Tlist -∗ isListSeg p p' null x xs Tint32 -∗
                 pt' ↦ null @ Tlist -∗ Φ void)
    ⊢ WP (while [! pt' @ Tlist != null](! pt' @ Tlist != null)<{
            pt <- ! pt' @ Tlist ;; pt' <- snd ! ! pt' @ Tlist @ (tcell Tint32)
          }>) {{ Φ }}.
  Proof.
    induction xs2 as [|x' xs2' IHxs']; iIntros (???????) "(Hlx&Hpt&Hpt'&Hxs1&Hxs2&%&HΦ)".
    - iDestruct "Hxs2" as "%". subst.
      wp_run. rewrite (right_id_L _ (++)).
      by iSpecialize ("HΦ" $! p' with "Hlx Hpt Hxs1 Hpt'").
    - simpl. wp_load. iDestruct "Hxs2" as (p'' l'') "[% [? ?]]".
      destruct_ands. subst. wp_op. iApply wp_while_true.
      iNext. wp_load. wp_assign. wp_load. wp_load.
      wp_snd. iNext. wp_assign.
      iApply (IHxs' (xs1 ++ [x'])); last iFrame; auto.
      iSplitL.
      { iApply lseg_snoc=>//. iFrame. }
      { by rewrite -assoc. }
  Qed.

  Definition enq_list (lx: val) (v: val) : expr :=
    let: t ::: Tlist := Ealloc Tlist (!lx@Tlist) in
    Eif (t != null) (
      let: t' ::: Tlist := Ealloc Tlist (snd (!?t)) in
      while [ t' != null ] (t' != null) <{
        t <- t';;
        t' <- snd (!?t')
      }> ;;
      snd !?t <- Ealloc (tcell Tint32) (Vpair v null)
    ) (* else *) (
      lx <- Ealloc (tcell Tint32) (Vpair v null)
    ).

  Lemma enq_spec Φ lx xs v: typeof v Tint32 → ∀ l,
    lx ↦ l @ Tlist ∗ isList l xs Tint32 ∗
    (∀ l', (lx ↦ l' @ Tlist) -∗ (isList l' (xs ++ [v]) Tint32) -∗ Φ void)
    ⊢ WP enq_list lx v {{ v, Φ v }}.
  Proof.
    intros ?. rewrite /enq_list. subst.
    unfold Edecl. iIntros (l) "[Hlx [Hl HΦ]]". wp_load.
    iDestruct (mapsto_typeof with "Hlx") as "%".
    wp_alloc pt as "Ht". wp_let. destruct xs as [|x xs'] eqn:?; subst.
    - simpl. iDestruct "Hl" as "%". subst. wp_run. iApply wp_if_false.
      wp_run. wp_alloc p as "Hp"=>//.
      wp_assign. iApply ("HΦ" with "[-Hp]")=>//.
      iExists _, _. iFrame. iSplit=>//.
    - simpl. wp_load. iDestruct "Hl" as (p l') "[% [? ?]]".
      destruct_ands. subst.
      wp_op. iApply wp_if_true.
      iNext. wp_load. wp_load. wp_snd. iNext.
      wp_alloc pt' as "Hpt'". wp_let.
      iApply wp_seq=>//.
      iApply (enq_spec' lx p _ x _ _ [] pt pt' p l'); last iFrame; auto.
      iSplitL "~".
      { simpl. iExists _. iSplit=>//. }
      iSplit=>//. iIntros (?) "? ? ? ?".
      wp_skip. destruct a. wp_load. wp_op.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval $ Byte.repr 4)) with 4%nat; last done.
      iDestruct (lseg_unsnoc with "~2") as "[H|[% Hp]]".
      + iDestruct "H" as (???) "[Hl [Hp %]]". destruct_ands. subst.
        iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
        wp_alloc lp' as "Hlp'"=>//. wp_assign.
        iApply ("HΦ" with "~").
        iDestruct (mapsto_typeof with "Hp1") as "%".
        iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp"; first by iSplitL "Hp1".
        iDestruct (lseg_snoc with "[Hl Hp]") as "Hl'"; try iFrame; auto.
        iDestruct (lseg_snoc with "[Hl' Hlp']") as "Hl''"; try iFrame; auto.
        iDestruct (lseg_to_list with "Hl''") as "Hl''".
        simpl. iDestruct "Hl''" as (??) "[% [? ?]]". destruct_ands. simplify_eq.
        iExists _, _. iFrame. done.
      + destruct_ands. subst.
        iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
        wp_alloc lp' as "Hlp'"=>//. wp_assign.
        iApply ("HΦ" with "~").
        iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp"; first by iSplitL "Hp1".
        iExists _, _. iFrame. iSplit=>//.
        iExists _, _. iFrame. iSplit=>//.
  Qed.

  Lemma rev_spec' (f: ident) ks Φ px py pt xs:
    ∀ lx ly ys,
      isList lx xs Tint32 ∗
      isList ly ys Tint32 ∗
      (∀ ly' : val, isList ly' (rev xs ++ ys) Tint32 -∗ own_stack ([] :: ks) -∗ Φ void) ∗
      own_stack ([] :: ks) ∗
      px ↦ lx @ Tlist ∗
      py ↦ ly @ Tptr Tvoid ∗
      pt ↦ - @ Tptr Tlist
      ⊢ WP while [! px @ Tlist != null](! px @ Tlist != null) <{
             pt <- snd ! ! px @ Tlist @ (tcell Tint32) ;;
             ! px @ Tlist + (Byte.repr 4) <- ! py @ (Tptr Tvoid) ;;
             py <- ! px @ Tlist ;;
             px <- ! pt @ (Tptr Tlist) }> {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs']; intros ??? ; subst.
    - iIntros "(Hlx & Hly & HΦ & Hs & Hpx & Hpy & Hpt)".
      iDestruct "Hlx" as "%". wp_run.
      { by simplify_eq. } wp_run.
      iApply ("HΦ" with "[-Hs]")=>//.
    - iIntros "(Hlx & Hly & HΦ & Hs & Hpx & Hpy & Hpt)".
      wp_load. iDestruct "Hlx" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      wp_run. iDestruct "Hpt" as (?) "Hpt".
      wp_assign. wp_load. destruct p as [pb po]. wp_op.
      rewrite /offset_by_byte.
      replace (Z.to_nat (Byte.intval $ Byte.repr 4)) with 4%nat; last done.
      wp_load.
      iDestruct (isList_ptr with "Hly") as "%". unfold tcell.
      iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
      wp_assign. wp_load. wp_assign. wp_load. wp_assign.
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      iFrame. iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp".
      { iSplitL "Hp1"; by simpl. }
      iSplitL "Hp Hly".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. split; [|split]=>//. by eapply typeof_any_ptr. }
      iSplitL "HΦ"; last eauto.
      by rewrite -app_assoc.
  Qed.

  Lemma rev_spec (f: ident) ks Φ xs:
    ∀ lx ly ys,
      text_interp f (Function Tvoid ps rev_list) ∗
      isList lx xs Tint32 ∗ isList ly ys Tint32 ∗ own_stack ks ∗
      (∀ ly', isList ly' (rev xs ++ ys) Tint32 -∗ own_stack ([]::ks) -∗ Φ Vvoid)
      ⊢ WP Ecall_typed Tvoid f [Evalue lx ; Evalue ly] {{ Φ }}.
   Proof.
    iIntros (???) "(Hf & Hlx & Hly & Hs & HΦ)". unfold rev_list.
    iApply (wp_call [] [lx; ly]); last iFrame; first by simpl.
    iNext. iIntros "Hs'".
    iDestruct (isList_ptr with "Hly") as "%".
    iDestruct (isList_ptr' with "Hlx") as "%".
    wp_alloc px as "Hpx". wp_let.
    wp_alloc py as "Hpy". wp_let.
    wp_alloc pt as "Hpt". wp_let.
    iApply (rev_spec' f ks Φ px py pt xs lx ly ys). iFrame. eauto.
  Qed.

End proof.
