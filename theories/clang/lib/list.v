(* Singly linked list *)

From iris.base_logic.lib Require Export wsat.
From iris_c.clang Require Import logic tactics notations.
From iris_c.lib Require Import gmap_solve int.

Section proof.
  Context `{clangG Σ}.

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

  Notation "'Tlist'" := (Tptr (tcell Tint8)).

  Definition rev_list : expr :=
    while: ( (!"x"@Tlist) != null ) (
      "t" <- snd (!(!"x"@Tlist)@(tcell Tint8)) ;;
      (!"x"@Tlist) + 1 <- !"y"@Tlist ;;
      "y" <- !"x"@Tlist ;;
      "x" <- !"t"@Tlist
    ) ;;
    return: !"y"@Tlist.

  Definition traverse_list (lx: val) : expr :=
    while: (!lx@Tlist != null) ( lx <- snd (!(!lx@Tlist)@(tcell Tint8)) ).

  Lemma traverse_spec Φ lx xs: ∀ l,
    lx ↦ l @ Tlist ∗ isList l xs Tint8 ∗ (isList l xs Tint8 -∗ Φ void)
    ⊢ WP (traverse_list lx, ([], semp)) {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - iIntros (l) "[? [% HΦ]]".
      rewrite /traverse_list. subst.
      iApply (wp_while [] []).
      repeat wp_step.
      iApply (wp_break [] []).
      simpl. iApply wp_value=>//.
      by iApply "HΦ".
    - iIntros (l) "[Hlx [Hl HΦ]]".
      simpl. iDestruct "Hl" as (p l') "[% [Hp Hl']]".
      destruct_ands.
      rewrite /traverse_list.
      iApply (wp_while [] []).
      do 10 wp_step.
      iApply (wp_continue [] []).
      iApply IHxs'. iFrame. iIntros "?".
      iApply "HΦ". iExists _, _. by iFrame.
  Qed.

  Lemma lseg_snoc' v:
    typeof v Tint8 →
    ∀ xs x p p' (p'': addr) l'',
      typeof l'' Tlist →
      isListSeg p p' p'' x xs Tint8 ∗ p'' ↦ Vpair v l'' @ tcell Tint8
       ⊢ isListSeg p p'' l'' x (xs ++ [v]) Tint8.
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
    typeof v Tint8 → typeof l'' Tlist →
    isListSeg p p' p'' x xs Tint8 ∗ p'' ↦ Vpair v l'' @ tcell Tint8
    ⊢ isListSeg p p'' l'' x (xs ++ [v]) Tint8.
  Proof. iIntros (??) "?". iApply lseg_snoc'=>//. Qed.

  Lemma lseg_unsnoc: ∀ xs p (p': addr) x,
    isListSeg p p' null x xs Tint8 ⊢
    (∃ (x': val) xs' p'', isListSeg p p'' p' x xs' Tint8 ∗
     p' ↦ Vpair x' null @ tcell Tint8 ∗ ⌜ xs = xs' ++ [x'] ⌝ ) ∨
    (⌜ p = p' ∧ xs = [] ⌝ ∗ p' ↦ Vpair x null @ tcell Tint8).
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
    isListSeg p p' null x xs Tint8 ⊢ isList p (x::xs) Tint8.
  Proof.
    induction xs as [|x' xs' IHxs'].
    - iDestruct 1 as (?) "[% ?]". destruct_ands.
      iExists _, _. iFrame. iSplit=>//.
    - simpl. iDestruct 1 as (??) "[% [? ?]]". destruct_ands.
      iDestruct (IHxs' with "~") as "?".
      iExists _, _. iFrame. iSplit=>//.
  Qed.

  Definition enq_env pt pt': env :=
    (sset "lt'" (Tlist, Vptr pt')
          (sset "lt" (Tptr Tlist, Vptr pt)
                semp)).

  Lemma enq_spec' lx (p: addr) Φ x xs k: ∀ xs2 xs1 pt pt' (p': addr) l',
    typeof l' Tlist → typeof p Tlist →
    lx ↦ p @ Tlist ∗ pt ↦ p' @ Tlist ∗ pt' ↦ l' @ Tlist ∗
    isListSeg p p' l' x xs1 Tint8 ∗ isList l' xs2 Tint8 ∗ ⌜ xs = xs1 ++ xs2 ⌝ ∗
    (∀ p': addr, lx ↦ p @ Tlist -∗ pt ↦ p' @ Tlist -∗
                 isListSeg p p' null x xs Tint8 -∗
                 pt' ↦ null @ Tlist -∗
                 WP (fill_ectxs void k, ([], enq_env pt pt')) {{ Φ }})
    ⊢ WP (fill_ectxs (while: (! "lt'" @ Tlist != null) (
            "lt" <- ! "lt'" @ Tlist ;; "lt'" <- snd ! ! "lt'" @ Tlist @ (tcell Tint8)
          )) k, ([], enq_env pt pt')) {{ Φ }}.
  Proof.
    induction xs2 as [|x' xs2' IHxs'];
      iIntros (???????) "(Hlx&Hpt&Hpt'&Hxs1&Hxs2&%&HΦ)".
    - iDestruct "Hxs2" as "%". subst.
      iApply wp_while. iNext. wp_run.
      rewrite (right_id_L _ (++)).
      iApply (wp_break _ []). simpl.
      by iSpecialize ("HΦ" $! p' with "Hlx Hpt Hxs1 Hpt'").
    - simpl. iDestruct "Hxs2" as (p'' l'') "[% [? ?]]". destruct_ands.
      iApply wp_while. iNext.
      wp_run. iApply (wp_continue _ []).
      iApply (IHxs' (xs1 ++ [x'])); last iFrame; auto.
      iSplitL.
      { iApply lseg_snoc=>//. iFrame. }
      { by rewrite -assoc. }
  Qed.

  Definition enq_list (lx: val) (v: val) : expr :=
    "lt" <- !lx @ Tlist ;;
    if: ((!"lt"@Tlist) != null) then: (
      "lt'" <- snd (!(!"lt"@Tlist)@(tcell Tint8)) ;;
      while: ((!"lt'"@Tlist) != null) (
        "lt" <- !"lt'"@Tlist;;
        "lt'" <- snd (!(!"lt'"@Tlist)@(tcell Tint8))
      ) ;;
      (!"lt"@Tlist) + 1 <- Ealloc (tcell Tint8) (Vpair v null)
    ) else: (
      lx <- Ealloc (tcell Tint8) (Vpair v null)
    ).

  Lemma enq_spec Φ lx lt lt' xs v: typeof v Tint8 → ∀ l,
    lt' ↦ null @ Tlist ∗ lt ↦ null @ Tlist ∗
    lx ↦ l @ Tlist ∗ isList l xs Tint8 ∗
    (∀ l', (lx ↦ l' @ Tlist) -∗ (isList l' (xs ++ [v]) Tint8) -∗ Φ void)
    ⊢ WP (enq_list lx v, ([], enq_env lt lt')) {{ v, Φ v }}.
  Proof.
    intros ?. rewrite /enq_list. subst.
    iIntros (l) "(Ht' & Ht & Hlx & Hl & HΦ)".
    iDestruct (mapsto_typeof with "Hlx") as "%". wp_var.
    destruct xs as [|x xs'] eqn:?; subst; simpl.
    - iDestruct "Hl" as "%". subst. wp_run.
      wp_alloc x as "Hx"=>//.
      wp_assign. iApply ("HΦ" with "[-Hx]")=>//.
      iExists _, _. iFrame. iSplit=>//.
    - simpl. iDestruct "Hl" as (p l') "[% [? ?]]".
      destruct_ands. wp_run.
      wp_unfill (Ewhile _ _).
      iApply (enq_spec' lx p _ x _ _ _ [] lt lt' p l'); last iFrame; auto.
      iSplitL "~"=>//.
      { simpl. iExists _. iSplit=>//. }
      iSplit=>//. iIntros (?) "? ? ? ?". destruct a. simpl.
      wp_run. rewrite_byte. replace (Z.to_nat 1) with 1%nat=>//.
      iDestruct (lseg_unsnoc with "~2") as "[H|[% Hp]]".
      + iDestruct "H" as (???) "[Hl [Hp %]]". destruct_ands.
        iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
        wp_alloc lp' as "Hlp'"=>//.
        wp_assign. iApply ("HΦ" with "~").
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

  Definition rev_env px py pt : env :=
    sset "x" (Tptr Tlist, Vptr px)
         (sset "y" (Tptr Tlist, Vptr py)
               (sset "t" (Tptr Tlist, Vptr pt) semp)).

  Lemma rev_spec' (f: ident) k ks Φ px py pt xs:
    ∀ lx ly ys,
      isList lx xs Tint8 ∗
      isList ly ys Tint8 ∗
      px ↦ lx @ Tlist ∗
      py ↦ ly @ Tlist ∗
      pt ↦ - @ Tlist ∗
      (∀ ly' : val, py ↦ ly' @ Tlist ∗
                    isList ly' (rev xs ++ ys) Tint8 -∗
                    WP (fill_ectxs void k, (ks, rev_env px py pt)) {{ Φ }})
      ⊢ WP (fill_ectxs (while: (! "x" @ Tlist != null) (
             "t" <- snd ! ! "x" @ Tlist @ (tcell Tint8) ;;
             ! "x" @ Tlist + (Byte.repr 1) <- ! "y" @ Tlist ;;
             "y" <- ! "x" @ Tlist ;;
             "x" <- ! "t" @ Tlist )) k, (ks, rev_env px py pt)) {{ v, Φ v }}.
  Proof.
    induction xs as [|x xs' IHxs']; intros ??? ; subst.
    - iIntros "(Hlx & Hly & Hpx & Hpy & Hpt & HΦ)".
      iDestruct "Hlx" as "%". subst. 
      iApply wp_while. iNext.
      wp_run. iApply (wp_break _ []).
      iApply ("HΦ" with "[-]")=>//. iFrame.
    - iIntros "(Hlx & Hly & Hpx & Hpy & Hpt & HΦ)".
      iDestruct "Hlx" as (p l') "(% & Hp & Hl')".
      destruct H0 as [? [? ?]]. subst.
      iDestruct "Hpt" as (?) "Hpt".
      destruct p as [pb po].
      iDestruct (isList_ptr with "Hly") as "%".
      iApply wp_while. iNext. wp_run.
      rewrite_byte. replace (Z.to_nat 1) with 1%nat; last done.
      iDestruct (mapstoval_split with "Hp") as "[Hp1 Hp2]". simpl.
      wp_run. iApply (wp_continue _ []).
      iApply (IHxs' l' (Vptr (pb, po)) (x::ys)).
      iFrame. iDestruct (mapstoval_join with "[Hp1 Hp2]") as "Hp".
      { iSplitL "Hp1"; by simpl. }
      iSplitL "Hp Hly".
      { iExists (pb, po), ly. iFrame.
        iPureIntro. split; [|split]=>//. by eapply typeof_any_ptr. }
      rewrite -app_assoc. iFrame. by iExists _.
  Qed.

  Definition ps :=
    [ ("x", Tptr Tlist); ("y", Tptr Tlist); ("t", Tptr Tlist) ].

  Lemma rev_spec pt k ks Φ xs:
    ∀ lx ly ys,
      "rev" T↦ Function Tvoid ps rev_list ∗
      isList lx xs Tint8 ∗ isList ly ys Tint8 ∗
      pt ↦ - @ Tlist ∗
      (∀ ly', isList ly' (rev xs ++ ys) Tint8 -∗ WP (fill_ectxs ly' k, ks) {{ Φ }})
      ⊢ WP (fill_ectxs (Ecall Tvoid "rev"
                              (Epair (Ealloc Tlist (Evalue lx))
                                     (Epair (Ealloc Tlist (Evalue ly))
                                            (Vpair pt void))))
                              k, ks) {{ Φ }}.
   Proof.
     iIntros (???). iIntros "(Hf & Hlx & Hly & Hpt & HΦ)".
     destruct ks.
     iDestruct (wp_bind (k ++ [ EKcall Tvoid "rev" 
                                ; EKpairl (Epair (Ealloc Tlist ly) (Vpair pt void))])
                        _ (Ealloc Tlist lx))
       as "H"=>//.
     assert (fill_ectxs (Ealloc Tlist lx)
                        (k ++ [ EKcall Tvoid "rev";
                                EKpairl (Epair (Ealloc Tlist ly) (Vpair pt void))]) =
             fill_ectxs (fill_ectxs (Ealloc Tlist lx)
                              [ EKcall Tvoid "rev";
                                EKpairl (Epair (Ealloc Tlist ly) (Vpair pt void))]) k).
     { symmetry. eapply fill_app. }
     rewrite H0.
     simpl. iApply "H".
     iDestruct (isList_ptr' with "Hlx") as "%".
     iDestruct (isList_ptr' with "Hly") as "%".
     wp_alloc x as "Hx". iApply wp_value=>//.
     rewrite -(fill_app x [EKcall Tvoid "rev";
                       EKpairl (Epair (Ealloc Tlist ly) (Vpair pt void))] k).
     simpl.
     rewrite (fill_app (Ealloc Tlist ly)
                       [EKcall Tvoid "rev"; EKpairr x; EKpairl (Vpair pt void) ] k).
     iApply wp_bind=>//.
     wp_alloc y as "Hy".
     iApply wp_value=>//.
     rewrite -(fill_app y [ EKcall Tvoid "rev";
                            EKpairr x;
                            EKpairl (Vpair pt void) ] k).
     simpl.
     rewrite (fill_app (Epair y (Vpair pt void))
                       [EKcall Tvoid "rev"; EKpairr x] k).
     iApply wp_bind=>//.
     iApply wp_pair.
     rewrite -(fill_app (Vpair y (Vpair pt void))
                        [EKcall Tvoid "rev"; EKpairr x] k).
     simpl.
     rewrite (fill_app (Epair x (Vpair y (Vpair pt void)))
                       [EKcall Tvoid "rev"] k).
     iApply wp_bind=>//. iApply wp_pair.
     rewrite -(fill_app (Vpair x (Vpair y (Vpair pt void)))
                        [EKcall Tvoid "rev"] k).
     simpl.
     iApply (wp_call (rev_env x y pt) e _
                     (Vpair x (Vpair y (Vpair pt Vvoid))) ps)=>//.
     iFrame. iNext.
     move: (rev_spec' "rev" [EKseq (return: ! "y" @ Tlist)]
                      (Kcall k e :: s) Φ x y pt xs lx ly ys) => Hspec.
     simpl in *.
     iDestruct (Hspec with "[-]") as "Hspec"=>//.
     { iFrame. iIntros (?).
       iIntros "[Hy Hl]".
       wp_run. by iApply "HΦ". }
   Qed.
End proof.
