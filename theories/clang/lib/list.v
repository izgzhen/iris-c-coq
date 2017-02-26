(* Singly linked list *)

From iris_os.clang Require Import logic tactics notations.
Require Import lib.gmap_solve.

Section proof.
  Context `{clangG Σ}.

  Fixpoint isList (l: val) (xs: list val) (t: type) :=
    match xs with
      | [] => (⌜ l = null ⌝)%I
      | x::xs' => (∃ p l',
                     ⌜ l = Vptr p ∧ typeof t x ⌝ ∗
                     p ↦ Vpair x l' @ (Tprod t (Tptr t)) ∗ isList l' xs' t)%I
    end.

  Parameter y t px: addr.
  Parameter x: ident.

  (* de brujin with autosubst? *)
  Definition tcell (telem: type): type := Tmu 0 (Tprod telem (Tptr (Tvar 0))).
  Definition tlist (telem: type): type := Tptr (tcell telem).

  Definition rev_list (telem: type) : stmts :=
    y <- null ;;
    while [ x != null ] ( x != null ) <{
      t <- snd (!x) ;;
      snd (!x) <- !y ;;
      y <- x ;;
      x <- !t
    }>;;
    x <- !y.

  Lemma rev_spec l ety Φ Φret body xs:
    instantiate_f_body {[ x := (tlist ety, px) ]} (rev_list ety) = Some body →
    isList l xs ety ∗ y ↦ - ∗ t ↦ - ∗ px ↦ l @ tlist ety ∗
    (isList l (rev xs) ety -∗ Φ Vvoid)
    ⊢ WP curs body {{ Φ; Φret }}.
  Proof.
    induction xs as [|x xs' IHxs'].
    - iIntros (?) "(% & Hy & Ht & Hpx & HΦ)".
      rewrite /instantiate_f_body /resolve_rhs map_to_list_singleton in H0.
      simpl in H0.
      destruct (decide (x = x))=>//.
      destruct px. gmap_solve.
      iDestruct "Hy" as (??) "Hy".
      wp_assign. wp_load.
      wp_op. simpl.
      iApply wp_while_false.
      iNext. wp_load. wp_assign.
      by iApply "HΦ".
    - 
    
    
  
End proof.
