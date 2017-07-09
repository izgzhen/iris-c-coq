From iris_c.clang Require Import notations lang logic tactics.
From iris_c.lib Require Import int.

Section proof.
  Context `{clangG Σ}.

  Definition f : expr :=
    if: ("x" != 0)
    then: (
      "x" <- "x" - 1 ;;
      Ecall Tvoid "g" (Epair (Evar "x") (Evalue Vvoid)) ;;
      return: void)
    else: ( return: void ).

  Definition g : expr :=
    if: ("x" != 0)
    then: (
      "x" <- "x" - 1 ;;
      Ecall Tvoid "f" (Epair (Evar "x") (Evalue Vvoid));;
      return: void)
    else: ( return: void ).

  Lemma rec_example (n: nat) k ks Φ:
    "f" T↦ Function Tvoid [("x", Tint32)] f ∗
    "g" T↦ Function Tvoid [("x", Tint32)] g ∗ Φ void
    ⊢ WP (fill_ectxs (Ecall Tvoid "f"
                            (Evalue (Vpair (Vint32 n) Vvoid))) k, ks) {{ Φ }}.
  Proof.
    iIntros "[#? [#? HΦ]]".
    iLöb as "IH" forall (n k ks Φ).
    destruct n eqn:?; subst.
    - admit. (* simple base case *)
    - iApply (wp_call _ (Vpair (Vint32 (S n0)) Vvoid)); last iFrame "#"; first done.
      iNext. wp_alloc ln as "Hln".
      wp_let. wp_load. wp_op.
      { instantiate (1:=vtrue). admit. }
      wp_step. iNext. wp_load. wp_op.
      replace (Z.pos (Pos.of_succ_nat n0) - 1%Z)%int with (Int.repr n0); last admit.
      wp_assign.
      iApply (wp_bind [EKseq _; EKcall _ _])=>//.
      admit.
      (* wp_load. iApply wp_value=>//. *)
      (* wp_unfill (Ecall _ _ _). *)
      (* iApply (wp_call [EKseq (return: void)] [Vint32 n0]); *)
      (*   last iFrame "#"; first done. *)
      (* iNext. wp_alloc lx as "Hlx". *)
      (* wp_let. wp_load. *)
      (* destruct n0 eqn:?; subst. *)
      (* + admit. *)
      (* + replace (S n != 0%Z)%E with (Evalue vtrue); last admit. *)
      (*   do 5 wp_step. wp_unfill (Ecall _ _ _)%E. *)
      (*   simpl. *)
      (*   replace (! lx @ Tint32)%E with *)
      (*   (Evalue $ (n - 1)); last admit. wp_unfill (Ecall _ _ _)%E. *)
      (*   iApply ("IH" $! (n - 1)). done. *)
  Admitted.
    
End proof.
