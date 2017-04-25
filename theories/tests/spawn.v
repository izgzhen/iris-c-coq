From iris_c.clang Require Import logic notations tactics.
From iris_c.clang.lib Require Import lock.
From iris_c.lib Require Import int.

Section test.
  Context `{clangG Σ, lockG Σ} (N: namespace) (γ: gname).

  Variable lx : addr.
  Variable l : val.
  Definition f_acquire : ident := 3.
  Definition f_release : ident := 4.
  Definition f_add : ident := 5.

  Definition R: iProp Σ := (∃ vx: int32, lx ↦ vx @ Tint32)%I.
  
  Definition add: expr :=
    Ecall Tvoid f_acquire [Evalue l] ;;
    lx <- !lx@Tint32 + 1;;
    Ecall Tvoid f_release [Evalue l].

  Lemma add_safe ks:
    is_lock N γ l R ∗
    text_interp f_release (Function Tvoid [(x, tylock)] release) ∗
    text_interp f_acquire (Function Tvoid [(x, tylock)] acquire)
    ⊢ WP (add, ks) {{ _, True }}.
  Proof.
    iIntros "(#Hlk & H1 & H2)". unfold add.
    wp_unfill (Ecall _ _ _).
    iApply acquire_spec. iFrame. iFrame "#".
    iIntros "Hlked HR".
    iDestruct "HR" as (?) "Hvx".
    wp_skip. wp_load. wp_op. wp_assign.
    iApply (release_spec []). iFrame "Hlk".
    iFrame. iSplitL "Hvx"; first by iExists _.
    iApply wp_value=>//.
  Qed.

  (* It is just DRF property -- though we can have a stronger spec
     by encoding some receipt tokens *)

  Definition spawn: expr :=
    Efork Tvoid f_add [] ;;
    Efork Tvoid f_add [].

  Lemma spawn_spec ks:
    is_lock N γ l R ∗
    text_interp f_release (Function Tvoid [(x, tylock)] release) ∗
    text_interp f_acquire (Function Tvoid [(x, tylock)] acquire) ∗
    text_interp f_add (Function Tvoid [] add)
    ⊢ WP (spawn, ks) {{ _, True }}.
  Proof.
    iIntros "(#Hlk & Hf1 & Hf2 & Hf3)".
    unfold spawn. iApply wp_seq=>//.
    iDestruct (text_interp_dup with "Hf3") as "[Hf3 ?]".
    iApply (wp_fork _ _ _ []); last iFrame; first done.
    iNext. iDestruct (text_interp_dup with "Hf1") as "[Hf1 Hf1']".
    iDestruct (text_interp_dup with "Hf2") as "[Hf2 Hf2']".
    iSplitL "Hf1 Hf2 Hf3".
    - wp_skip. iApply (wp_fork _ _ _ []); last iFrame; first done.
      iNext. iSplit=>//. iApply add_safe. by iFrame.
    - iApply add_safe. by iFrame.
  Qed.

End test.
