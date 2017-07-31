From iris_c.clang Require Import logic notations tactics.
From iris_c.clang.lib Require Import lock.
From iris_c.lib Require Import int.

Section test.
  Context `{clangG Σ, lockG Σ} (N: namespace) (γ: gname).

  Variable lx : addr.
  Variable l : val.

  Definition R: iProp Σ := (∃ vx: int8, lx ↦ vx @ Tint8)%I.
  
  Definition add: expr :=
    Ecall Tvoid "acquire" (Evalue (Vpair l Vvoid)) ;;
    lx <- !lx@Tint8 + 1;;
    Ecall Tvoid "release" (Evalue (Vpair l Vvoid)).

  Lemma add_safe ks:
    is_lock N γ l R ∗
    "release" T↦ Function Tvoid [("x", tylock)] release ∗
    "acquire" T↦ Function Tvoid [("x", tylock)] acquire
    ⊢ WP (add, ks) {{ _, True }}.
  Proof.
    iIntros "(#Hlk & #? & #?)". unfold add.
    wp_unfill (Ecall _ _ _).
    iApply acquire_spec. iFrame "#".
    iIntros "Hlked HR".
    iDestruct "HR" as (?) "Hvx".
    wp_skip. wp_load. wp_op. wp_assign.
    iApply (release_spec []). iFrame "Hlked Hlk". iFrame "#".
    iSplitL "Hvx"; first by iExists _.
    iApply wp_value=>//.
  Qed.

  (* It is just DRF property -- though we can have a stronger spec
     by encoding some receipt tokens *)

  Definition spawn: expr :=
    Efork Tvoid "add" ;;
    Efork Tvoid "add".

  Lemma spawn_spec ks:
    is_lock N γ l R ∗
    "release" T↦ Function Tvoid [("x", tylock)] release ∗
    "acquire" T↦ Function Tvoid [("x", tylock)] acquire ∗
    "add" T↦ Function Tvoid [] add
    ⊢ WP (spawn, ks) {{ _, True }}.
  Proof.
    iIntros "(#Hlk & #? & #? & #?)".
    unfold spawn. iApply wp_seq=>//.
    iApply (wp_fork _ _ _). iFrame "#".
    iSplitL ""; iNext.
    - wp_skip. iApply (wp_fork _ _ _); iFrame "#".
      iSplit=>//; iNext=>//. iApply add_safe. iFrame "#".
    - iApply add_safe. iFrame "#".
  Qed.

End test.
