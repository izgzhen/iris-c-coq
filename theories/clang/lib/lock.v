From iris_c.clang Require Import logic notations tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.

(* Spin lock *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].

Section spin_lock.

  Definition acquire : expr :=
    while: (ECAS tybool "x" vfalse vtrue == vfalse ) ( void ) ;;
    return: void.

  Definition newlock : expr :=
    return: Ealloc tybool vfalse.

  Definition release : expr :=
    !?"x" <- vfalse ;;
    return: void.

  Context `{!clangG Σ, !lockG Σ} (N: namespace).

  Definition lock_inv (γ : gname) (l : addr) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ b_to_v b @ tybool ∗
                 if b then True else own γ (Excl ()) ∗ R)%I.

  Definition tylock := Tptr tybool.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: addr, ⌜lk = Vptr l ∧ typeof lk tylock ⌝ ∧ inv N (lock_inv γ l R))%I.

  Definition locked (γ : gname): iProp Σ := own γ (Excl ()).

  Global Instance lock_inv_ne n γ l : Proper (dist n ==> dist n) (lock_inv γ l).
  Proof. solve_proper. Qed.

  Global Instance is_lock_ne n l : Proper (dist n ==> dist n) (is_lock γ l).
  Proof. solve_proper. Qed.

  (** The main proofs. *)
  Global Instance is_lock_persistent γ l R : PersistentP (is_lock γ l R).
  Proof. apply _. Qed.
  Global Instance locked_timeless γ : TimelessP (locked γ).
  Proof. apply _. Qed.

  Lemma locked_exclusive (γ : gname) : locked γ -∗ locked γ -∗ False.
  Proof. iIntros "H1 H2". by iDestruct (own_valid_2 with "H1 H2") as %?. Qed.

  Lemma is_lock_tylock γ l R: is_lock γ l R ⊢ ⌜ typeof l tylock ⌝.
  Proof. iIntros "Hlk". iDestruct "Hlk" as (?) "[% ?]". by destruct H0. Qed.

  Lemma newlock_spec (R: iProp Σ) Φ k ks:
    "newlock" T↦ Function (Tptr tybool) [] newlock ∗
    R ∗ (∀ γ lk, is_lock γ lk R -∗ WP (fill_ectxs lk k, ks) {{ Φ }})
    ⊢ WP (fill_ectxs (Ecall (Tptr tybool) "newlock" []) k, ks) {{ Φ }}.
  Proof.
    iIntros "(Hf & HR & HΦ)".
    iApply (wp_call k []); last iFrame; first done.
    iNext. rewrite /newlock /=.
    wp_alloc l as "Hl". iApply (wp_ret []).
    iFrame. iApply fupd_wp.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply ("HΦ" with "[-]")=>//. iExists _. iSplit=>//.
    iPureIntro. split=>//. constructor.
  Qed.

  Lemma acquire_spec k lk {γ R Φ ks}:
    "acquire" T↦ (Function Tvoid [("x", tylock)] acquire) ∗
    is_lock γ lk R ∗ (locked γ -∗ R -∗ WP (fill_ectxs void k, ks) {{ Φ }})
    ⊢ WP (fill_ectxs (Ecall Tvoid "acquire" [Evalue lk]) k, ks) {{ Φ }}.
  Proof.
    iIntros "(Hf & #Hlk & HΦ)".
    iApply (wp_call k [lk]); last iFrame; first done.
    iNext. iDestruct (is_lock_tylock with "Hlk") as "%".
    wp_alloc lkx as "Hlkx". wp_let.
    iLöb as "IH".
    wp_unfill (Ewhile _ _).
    iApply wp_while. iNext.
    iDestruct "Hlk" as (l) "[% ?]". destruct_ands.
    wp_load.
    wp_bind (ECAS _ _ _ _).
    wp_atomic.
    iInv N as ([]) "[>Hl HR]" "Hclose"; iModIntro; simpl.
    - wp_cas_fail.
      iIntros "Hl".
      iMod ("Hclose" with "[-Hlkx HΦ]").
      { iNext. iExists true. iFrame. }
      iModIntro. do 4 wp_step.
      iApply (@wp_continue _ _ _ _ _ _ []). simpl.
      iApply ("IH" with "HΦ Hlkx").
    - wp_cas_suc.
      iIntros "Hl'".
      iMod ("Hclose" with "[-HΦ Hlkx HR]").
      { iNext. iExists true. iFrame. }
      iModIntro. wp_run.
      iApply (@wp_break _ _ _ _ []).
      iDestruct "HR" as "[Ho HR]". simpl.
      wp_run.
      iApply ("HΦ" with "[-HR]")=>//.
  Qed.

  Lemma release_spec k lk {γ R Φ ks}:
    "release" T↦ Function Tvoid [("x", tylock)] release ∗
    is_lock γ lk R ∗ locked γ ∗ R ∗ WP (fill_ectxs void k, ks) {{ Φ }}
    ⊢ WP (fill_ectxs (Ecall Tvoid "release" [Evalue lk]) k, ks) {{ Φ }}.
  Proof.
    iIntros "(Hf & #Hlk & Hlked & HR & HΦ)".
    iDestruct "Hlk" as (l) "[% ?]". destruct_ands.
    iApply (wp_call k [Vptr l]); last iFrame; auto.
    iIntros "!>". wp_alloc lkx as "Hlkx". wp_let. wp_bind (_ <- _)%E.
    wp_load. wp_atomic.
    iInv N as ([]) "[>Hl HR']" "Hclose"; iModIntro.
    - simpl. iApply wp_assign; last iFrame; try by constructor.
      iIntros "!> Hl". iMod ("Hclose" with "[-HΦ]")=>//.
      + iExists false. iFrame.
      + iModIntro. wp_run. iFrame.
    - iDestruct "HR'" as "[>Ho' HR']".
      by iDestruct (locked_exclusive with "Hlked Ho'") as "%".
  Qed.

End spin_lock.

Arguments acquire_spec {_ _ _ _} _ {_ _ _ _ _}.
Arguments release_spec {_ _ _ _} _ {_ _ _ _ _}.
