From iris_c.clang Require Import logic notations tactics.

Section example.
  Context `{clangG Σ}.

  Definition swap (t: type) : expr :=
    let: "x" ::: t in
    "x" <- "a1" ;;
    "a1" <- "a2" ;;
    "a2" <- "x".

  (* Instantiate the variables *)
  Definition swap' t  (l1 l2: addr) :=
    instantiate_let "a1" l1 t (swap t) ≫= instantiate_let "a2" l2 t.
  
  Lemma swap_spec' t swap_e l1 l2 v1 v2 ks:
    swap' t l1 l2 = Some swap_e →
    {{{ l1 ↦ v1 @ t ∗ l2 ↦ v2 @ t }}} (swap_e, ks) {{{ RET void ; l1 ↦ v2 @ t ∗ l2 ↦ v1 @ t }}}.
  Proof.
    iIntros (H0 ?) "[??] HΦ". inversion H0. extract_types.
    wp_alloc lx as "Hlx". wp_run. iApply ("HΦ" with "[-]"). iFrame.
  Qed.

End example.
