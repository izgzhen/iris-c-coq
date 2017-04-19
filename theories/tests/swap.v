From iris_c.clang Require Import logic notations tactics.

Section example.
  Context `{clangG Σ}.

  Definition x: ident := 1.

  Definition Edecl (t: type) (x: ident) e : expr :=
    Elet_typed t x (Ealloc t (Evalue (default_val t))) e.
    
  Definition swap (t: type) (l1 l2: addr) :=
    Edecl t x
    (x <- ! l1 @ t ;; l1 <- !l2 @ t ;; l2 <- x).

  Lemma swap_spec t l1 l2 v1 v2 Φ :
    l1 ↦ v1 @ t ∗ l2 ↦ v2 @ t ∗
    (l1 ↦ v2 @ t -∗ l2 ↦ v1 @ t -∗ Φ void)
    ⊢ WP swap t l1 l2 {{ Φ }}.
  Proof.
    iIntros "(Hl1 & Hl2 & HΦ)".
    rewrite /swap /Edecl.
    iDestruct (mapsto_typeof with "Hl1") as "%".
    iDestruct (mapsto_typeof with "Hl2") as "%".
    wp_alloc lx as "Hlx". wp_let.
    wp_run. iApply ("HΦ" with "Hl1 Hl2").
  Qed.
  
End example.
