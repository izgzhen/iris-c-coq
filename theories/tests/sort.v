From iris_c.clang Require Import logic notations tactics.
From iris_c.clang.lib Require Import array.

Section sort.
  Context `{clangG Σ}.

  Definition i: ident := 1.
  Definition j: ident := 2.
  Variable l: addr.
  Definition k: ident := 4.
  Definition t: ident := 3.

  Coercion Int.repr : Z >-> int32.

  Definition coerce_nat_to_expr (i: nat) := Evalue (Vint32 (Int.repr i)).
  Coercion coerce_nat_to_expr: nat >-> expr.
  
  Definition shift: expr :=
    let: t ::: Tint32 := Ealloc Tint32 (index Tint32 l i) in
    let: k ::: Tint32 := Ealloc Tint32 (i - 1) in
    while [k != j - 1] (k != j - 1) <{
      index Tint32 l (k + 1) <- index Tint32 l k ;;
      k <- k - 1
    }>;;
    index Tint32 l k <- t.

  Inductive shift_array: nat → nat → list val → list val → Prop :=
  | ShiftArray:
      ∀ a1 a2 a3 x i l,
        length a1 = i → length a2 = l →
        shift_array i (i + l) (a1 ++ a2 ++ [x] ++ a3) (a1 ++ [x] ++ a2 ++ a3).
  
  Lemma shift_spec f (vi vj: nat) vs n Φ:
    text_interp f (Function Tvoid [(i, Tint32); (j, Tint32)] shift) ∗
    l ↦ varray vs @ tyarray Tint32 n ∗
    (∀ vs', ⌜ shift_array vi vj vs vs' ⌝ -∗ l ↦ varray vs' @ tyarray Tint32 n -∗ Φ void)
    ⊢ WP Ecall_typed Tvoid f (map coerce_nat_to_expr [vi; vj]) {{ Φ }}.
  Admitted.

  Fixpoint max_list (l: list nat) :=
    match l with
      | [] => O
      | x::l' => max x (max_list l')
    end.

  Inductive sorted: list nat → Prop :=
  | Sempty: sorted []
  | Sapp: ∀ x l, x > max_list l → sorted (x::l).

  Definition sort f (n: nat): expr :=
    let: i ::: Tint32 := Ealloc Tint32 1 in
    Edecl Tint32 j (
    while [i :<: n] (i :<: n) <{
      j <- 0 ;;
      while [j :<: i] (j :<: i) <{
        Eif (index Tint32 l i :<: index Tint32 l j) (
          Ecall_typed Tvoid f [Evar i; Evar j]
        ) void ;;
        j <- j + 1
      }> ;;
      i <- i + 1
    }>).

  (* Lemma sort_spec f1 f2 n vs Φ: *)
  (*   text_interp f1 (Function Tvoid [(i, Tint32); (j, Tint32)] shift) ∗ *)
  (*   text_interp f2 (Function Tvoid [] (sort f1 n)) ∗ *)
  (*   l ↦ varray vs @ tyarray Tint32 n ∗ *)
  (*   (∀ vs', ⌜ sorted vs' ∧ vs' vs ⌝ -∗ l ↦ varray vs' @ tyarray Tint32 n -∗ Φ void)     *)
  (*   ⊢ WP Ecall_typed Tvoid f2 [] {{ Φ }}. *)
  
End sort.
