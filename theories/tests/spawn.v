From iris_c.clang Require Import logic notations tactics.
From iris_c.clang.lib Require Import lock.
From iris_c.lib Require Import int.

Section test.
  Context `{clangG Σ, lockG Σ} (N: namespace) (γ: gname).

  Variable lx : addr.
  Variable l : val.
  Definition f_acquire : ident := 3.
  Definition f_release : ident := 4.

  Definition R: iProp Σ := (∃ vx: int32, lx ↦ vx @ Tint32)%I.
  
  Definition add: expr :=
    Ecall Tvoid f_acquire [Evalue l] ;;
    lx <- !lx@Tint32 + 1;;
    Ecall Tvoid f_release [Evalue l].

  Lemma add_safe (lr: addr) ks:
    own_stack ks ∗ is_lock N γ l R ∗
    text_interp f_release (Function Tvoid [(x, tylock)] release) ∗
    text_interp f_acquire (Function Tvoid [(x, tylock)] acquire)
    ⊢ WP add {{ _, True }}.
  Proof.
    iIntros "(Hs & #Hlk & H1 & H2)". unfold add.
    wp_unfill (Ecall _ _ _).
    iApply acquire_spec. iFrame. iFrame "#".
    iIntros "Hlked HR Hks".
    iDestruct "HR" as (?) "Hvx".
    wp_skip. wp_load. wp_op. wp_assign.
    iApply (release_spec []). iFrame "Hlk".
    iFrame. iSplitL "Hvx"; first by iExists _.
    iIntros "Hks". iApply wp_value=>//.
  Qed.

  (* It is just DRF property -- though we can have a stronger spec
     by encoding some receipt tokens *)

  