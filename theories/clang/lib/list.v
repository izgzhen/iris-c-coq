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

  (* Definition rev_list (x: val) : stmts := *)
  (*   y <- null ;; *)
  (*   while (x != null) { *)
  (*      t = !x *)
  (*   } *)
End proof.

