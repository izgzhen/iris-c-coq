(* Singly linked list *)

From iris_os.clang Require Import logic tactics notations.

Section proof.
  Context `{clangG Σ}.

  Fixpoint isList (l: val) (xs: list val) (t: type) :=
    match xs with
      | [] => True%I
      | x::xs' => (∃ p l',
                     ⌜ l = Vptr p ∧ typeof t x ⌝ ∗
                     p ↦ Vpair x l' @ (Tprod t (Tptr t)) ∗ isList l' xs' t)%I
    end.

  Parameter y t: addr.

  (* de brujin with autosubst? *)
  Definition tcell (telem: type): type := Tmu 0 (Tprod telem (Tptr (Tvar 0))).
  Definition tlist (telem: type): type := Tptr (tcell telem).
  
  Definition rev_list (x: val) (telem: type) : stmts :=
    y <- null ;;
    while ( x != null ) {{
      t <- snd (!x) ;;
      snd (!x) <- y ;;
      y <- x ;;
      x <- t
    }};;
    x <- y.

End proof.
