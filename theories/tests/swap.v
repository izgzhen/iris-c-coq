From iris_c.clang Require Import logic notations tactics.

Section example.
  Context `{clangG Σ}.

  Definition swap (t: type) : expr :=
    "x" <- !"a1"@t ;;
    "a1" <- !"a2"@t ;;
    "a2" <- !"x"@t.

  Definition senv t vx v1 v2 : env :=
    sset "x" (Tptr t, vx)
         (sset "a1" (Tptr t, v1)
               (sset "a2" (Tptr t, v2) semp)).
  
  Lemma swap_spec t l1 l2 lx v1 v2 ks:
    {{{ l1 ↦ v1 @ t ∗ l2 ↦ v2 @ t ∗ lx ↦ - @ t }}}
      (swap t, (ks, senv t lx l1 l2))
    {{{ RET void ; l1 ↦ v2 @ t ∗ l2 ↦ v1 @ t ∗ lx ↦ - @ t }}}.
  Proof.
    iIntros (?) "[?[??]] HΦ". iDestruct "~2" as (?) "?".
    extract_types.
    unfold swap.
    wp_var. wp_var. wp_run.
    wp_var. wp_var. wp_run.
    wp_var. wp_var. wp_run.
    iApply ("HΦ" with "[-]"). iFrame.
    by iExists _.
  Qed.

End example.
