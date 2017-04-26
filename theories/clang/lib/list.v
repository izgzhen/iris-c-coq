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
      by destruct_ands.
  Qed.

  Lemma isList_ptr' (l: val) (xs: list val) (t: type) :
    isList l xs t ⊢ ⌜ typeof l (Tptr (tcell t)) ⌝.
  Proof.
    destruct xs as [|x xs'].
    - iIntros "%". iPureIntro. by subst.
    - simpl. iIntros "H".
      iDestruct "H" as (??) "(% & ? & _)".
      by destruct_ands.
  Qed.

  Definition x: ident := 1.
  Definition y: ident := 2.
  Definition t: ident := 3.
  Definition t': ident := 4.

  Notation "'Tlist'" := (Tptr (tcell Tint32)).

  Definition rev_list : expr :=
    let: t ::: Tptr Tlist in
    while: ( x != null ) (
      t <- snd (!?x) ;;
      snd (!?x) <- y ;;
      y <- x ;;
      x <- t
    ) ;;
    return: y.

  Definition ps :=
    [ (x, Tlist); (y, Tptr Tvoid) ].

  Definition traverse_list (lx: val) : expr :=
    while: (!lx@Tlist != null) ( lx <- snd (!(!lx@Tlist)@(tcell Tint32)) ).

  Lemma traverse_spec Φ lx xs: ∀ l,
    lx ↦ l @ Tlist ∗ isList l xs Tint32 ∗ (isList l xs Tint32 -∗ Φ void)
    ⊢ WP (traverse_list lx, []) {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - iIntros (l) "[? [% HΦ]]".
      rewrite /traverse_list. subst.
      repeat wp_step. by iApply "HΦ".
    - iIntros (l) "[Hlx [Hl HΦ]]".
      simpl. iDestruct "Hl" as (p l') "[% [Hp Hl']]".
      destruct_ands.
      rewrite /traverse_list. do 9 wp_step.
      iApply IHxs'. iFrame. iIntros "?".
      iApply "HΦ". iExists _, _. by iFrame.
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
    - iDestruct "Hl" as (p''') "[% ?]". destruct_ands.
      iExists p''', p''. iSplit=>//. iFrame.
      iExists _. iFrame. done.
    - iDestruct "Hl" as (p''' l') "[% [? ?]]". destruct_ands.
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
    - iIntros (???) "H". simpl. iDestruct "H" as (?) "[% ?]". destruct_ands.
      iRight. simplify_eq. by iFrame.
    - iIntros (???) "H". simpl. iDestruct "H" as (??) "[% [? ?]]". destruct_ands.
      iDestruct (IHxs' with "~1") as "[?|[% ?]]".
      + iLeft. iDestruct "~2" as (???) "[? [? %]]". iExists H2. iFrame.
        subst. iExists (x'::H5). iExists _.
        iSplit=>//. simpl. iExists _, _.
        iFrame. done.
      + destruct_ands. iLeft. iExists x'. iFrame.
        iExists [], H0. iSplit=>//. simpl. iExists _.
        iSplit=>//.
  Qed.

  Lemma lseg_to_list xs: ∀ p p' x,
    isListSeg p p' null x xs Tint32 ⊢ isList p (x::xs) Tint32.
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iDestruct 1 as (?) "[% ?]". destruct_ands.
      iExists _, _. iFrame. iSplit=>//.
    - simpl. iDestruct 1 as (??) "[% [? ?]]". destruct_ands.
      iDestruct (IHxs' with "~") as "?".
      iExists _, _. iFrame. iSplit=>//.
  Qed.

  Lemma enq_spec' lx (p: addr) Φ x xs: ∀ xs2 xs1 pt pt' (p': addr) l',
    typeof l' Tlist → typeof p Tlist →
    lx ↦ p @ Tlist ∗ pt ↦ p' @ Tlist ∗ pt' ↦ l' @ Tlist ∗
    isListSeg p p' l' x xs1 Tint32 ∗ isList l' xs2 Tint32 ∗ ⌜ xs = xs1 ++ xs2 ⌝ ∗
    (∀ p': addr, lx ↦ p @ Tlist -∗ pt ↦ p' @ Tlist -∗ isListSeg p p' null x xs Tint32 -∗
                 pt' ↦ null @ Tlist -∗ Φ void)
    ⊢ WP (while: (! pt' @ Tlist != null) (
            pt <- ! pt' @ Tlist ;; pt' <- snd ! ! pt' @ Tlist @ (tcell Tint32)
          ), []) {{ Φ }}.
  Proof.
    induction xs2 as [|x' xs2' IHxs']; iIntros (???????) "(Hlx&Hpt&Hpt'&Hxs1&Hxs2&%&HΦ)".
    - iDestruct "Hxs2" as "%". subst.
      repeat wp_step. rewrite (right_id_L _ (++)).
      by iSpecialize ("HΦ" $! p' with "Hlx Hpt Hxs1 Hpt'").
    - simpl. iDestruct "Hxs2" as (p'' l'') "[% [? ?]]". destruct_ands.
      do 11 wp_step.
      iApply (IHxs' (xs1 ++ [x'])); last iFrame; auto.
      iSplitL.
      { iApply lseg_snoc=>//. iFrame. }
      { by rewrite -assoc. }
  Qed.

  Definition enq_list (lx: val) (v: val) : expr :=
    let: t ::: Tlist := Ealloc Tlist (!lx@Tlist) in
    if: (t != null) then: (
      let: t' ::: Tlist := Ealloc Tlist (snd (!?t)) in
      while: (t' != null) (
        t <- t';;
        t' <- snd (!?t')
      ) ;;
      snd !?t <- Ealloc (tcell Tint32) (Vpair v null)
    ) else: (
      lx <- Ealloc (tcell Tint32) (Vpair v null)
    ).
  
  Lemma enq_spec Φ lx xs v: typeof v Tint32 → ∀ l,
    lx ↦ l @ Tlist ∗ isList l xs Tint32 ∗
    (∀ l', (lx ↦ l' @ Tlist) -∗ (isList l' (xs ++ [v]) Tint32) -∗ Φ void)
    ⊢ WP (enq_list lx v, []) {{ v, Φ v }}.
  Proof.
    intros ?. rewrite /enq_list. subst.
    iIntros (l) "[Hlx [Hl HΦ]]".
    iDestruct (mapsto_typeof with "Hlx") as "%".
    wp_load. wp_alloc pt as "Ht". wp_let. destruct xs as [|x xs'] eqn:?; subst; simpl.
    - iDestruct "Hl" as "%". subst. wp_run. wp_alloc p as "Hp"=>//.
      wp_assign. iApply ("HΦ" with "[-Hp]")=>//.
      iExists _, _. iFrame. iSplit=>//.
    - simpl. iDestruct "Hl" as (p l') "[% [? ?]]".
      destruct_ands. wp_run.
      wp_alloc pt' as "Hpt'". wp_let.
      iApply wp_seq=>//.
      iApply (enq_spec' lx p _ x _ _ [] pt pt' p l'); last iFrame; auto.
      iSplitL "~".
      { simpl. iExists _. iSplit=>//. }
      iSplit=>//. iIntros (?) "? ? ? ?". destruct a.
      wp_run. rewrite_byte. replace (Z.to_nat 4) with 4%nat; last done.
      iDestruct (lseg_unsnoc with "~2") as "[H|[% Hp]]".
      + iDestruct "H" as (???) "[Hl [Hp %]]". destruct_ands.
        iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
        wp_alloc lp' as "Hlp'"=>//. wp_assign.
        iApply ("HΦ" with "~").
        iDestruct (mapsto_typeof with "Hp1") as "%".
        iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp"; first by iSplitL "Hp1".
        iDestruct (lseg_snoc with "[Hl Hp]") as "Hl'"; try iFrame; auto.
        iDestruct (lseg_snoc with "[Hl' Hlp']") as "Hl''"; try iFrame; auto.
        iDestruct (lseg_to_list with "Hl''") as "Hl''".
        simpl. iDestruct "Hl''" as (??) "[% [? ?]]". destruct_ands.
        iExists _, _. iFrame. done.
      + destruct_ands.
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
      (∀ ly' : val, py ↦ ly' @ Tptr Tvoid ∗ isList ly' (rev xs ++ ys) Tint32 -∗ Φ void) ∗
      px ↦ lx @ Tlist ∗
      py ↦ ly @ Tptr Tvoid ∗
      pt ↦ - @ Tptr Tlist
      ⊢ WP (while: (! px @ Tlist != null) (
             pt <- snd ! ! px @ Tlist @ (tcell Tint32) ;;
             ! px @ Tlist + (Byte.repr 4) <- ! py @ (Tptr Tvoid) ;;
             py <- ! px @ Tlist ;;
             px <- ! pt @ (Tptr Tlist) ), ks) {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs']; intros ??? ; subst.
    - iIntros "(Hlx & Hly & HΦ & Hpx & Hpy & Hpt)".
      iDestruct "Hlx" as "%". subst. wp_run.
      iApply ("HΦ" with "[-]")=>//. iFrame.
    - iIntros "(Hlx & Hly & HΦ & Hpx & Hpy & Hpt)".
      iDestruct "Hlx" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      iDestruct "Hpt" as (?) "Hpt".
      destruct p as [pb po].
      iDestruct (isList_ptr with "Hly") as "%".
      wp_run. rewrite_byte. replace (Z.to_nat 4) with 4%nat; last done.
      iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
      do 5 wp_step.
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      iFrame. iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp".
      { iSplitL "Hp1"; by simpl. }
      iSplitL "Hp Hly".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. split; [|split]=>//. by eapply typeof_any_ptr. }
      iSplitL "HΦ"; last eauto.
      by rewrite -app_assoc.
  Qed.

  Lemma rev_spec (f: ident) k ks Φ xs:
    ∀ lx ly ys,
      text_interp f (Function Tvoid ps rev_list) ∗
      isList lx xs Tint32 ∗ isList ly ys Tint32 ∗
      (∀ ly', isList ly' (rev xs ++ ys) Tint32 -∗ WP (fill_ectxs ly' k, ks) {{ Φ }})
      ⊢ WP (fill_ectxs (Ecall Tvoid f [Evalue lx ; Evalue ly]) k, ks) {{ Φ }}.
   Proof.
    iIntros (???) "(Hf & Hlx & Hly & HΦ)".
    iApply (wp_call _ [lx; ly]); last iFrame; first by simpl.
    iNext.
    iDestruct (isList_ptr with "Hly") as "%".
    iDestruct (isList_ptr' with "Hlx") as "%".
    wp_alloc px as "Hpx". wp_let.
    wp_alloc py as "Hpy". wp_let.
    wp_alloc pt as "Hpt". wp_let. iApply wp_seq=>//.
    iApply (rev_spec' f (k::ks)). iFrame.
    iSplitR "Hpt"; last by iExists _.
    iIntros (?) "[? ?]".
    wp_skip. wp_load. wp_ret. by iApply "HΦ".
  Qed.

End proof.
