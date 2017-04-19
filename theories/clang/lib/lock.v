From iris_c.clang Require Import logic notations tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.

(* Spin lock *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].

Section spin_lock.

  Parameter lk: val.

  Definition acquire : expr :=
    while [ECAS_typed tybool lk vfalse vtrue == vfalse]
          (ECAS_typed tybool lk vfalse vtrue == vfalse )
    <{ void }>.

  Definition newlock : expr :=
    return: Ealloc tybool vfalse.

  Definition release : expr :=
    lk <- vfalse.

  Context `{!clangG Σ, !lockG Σ} (N: namespace).

  Definition lock_inv (γ : gname) (l : addr) (R : iProp Σ) : iProp Σ :=
    (∃ b : bool, l ↦ b_to_v b @ tybool ∗
                 if b then True else own γ (Excl ()) ∗ R)%I.

  Definition is_lock (γ : gname) (lk : val) (R : iProp Σ) : iProp Σ :=
    (∃ l: addr, ⌜lk = Vptr l⌝ ∧ inv N (lock_inv γ l R))%I.

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

  Lemma newlock_spec' (R : iProp Σ) Φ k ks:
    own_stack (k::ks) ∗
    R ∗ (∀ γ lk, is_lock γ lk R -∗ own_stack ks -∗ WP fill_ectxs lk k {{ Φ }}) ⊢
    WP newlock {{ Φ }}.
  Proof.
    iIntros "(HS & HR & HΦ)".
    rewrite /newlock /=.
    wp_alloc l as "Hl". iApply (wp_ret []).
    iFrame. iIntros "Hs". iApply fupd_wp.
    iMod (own_alloc (Excl ())) as (γ) "Hγ"; first done.
    iMod (inv_alloc N _ (lock_inv γ l R) with "[-Hs HΦ]") as "#?".
    { iIntros "!>". iExists false. by iFrame. }
    iModIntro. iApply ("HΦ" with "[-Hs]")=>//. iExists l. eauto.
  Qed.

  Lemma newlock_spec (R: iProp Σ) f Φ k ks:
    text_interp f (Function (Tptr tybool) [] newlock) ∗
    R ∗ own_stack ks ∗ (∀ γ lk, own_stack ks -∗ is_lock γ lk R -∗ WP fill_ectxs lk k {{ Φ }})
    ⊢ WP fill_ectxs (Ecall_typed (Tptr tybool) f []) k {{ Φ }}.
  Proof.
    iIntros "(Hf & HR & Hs & HΦ)".
    iApply (wp_call k []); last iFrame; first done.
    iNext. iIntros "Hs'". iApply (newlock_spec' R). iFrame.
    iIntros (??) "Hlk". iIntros "Hs".
    iApply ("HΦ" with "[-Hlk]")=>//.
  Qed.

  Lemma acquire_spec γ R Φ:
    is_lock γ lk R ∗ (locked γ -∗ R -∗ Φ void)
    ⊢ WP acquire {{ Φ }}.
  Proof.
    iLöb as "IH".
    iIntros "[#Hlk HΦ]".
    unfold acquire.
    iDestruct "Hlk" as (l) "[% ?]". rewrite H.
    wp_bind (ECAS_typed _ _ _ _).
    iApply wp_atomic.
    { by apply atomic_enf. }
    iInv N as ([]) "[>Hl HR]" "Hclose"; iModIntro.
    - wp_cas_fail.
      iIntros "Hl".
      iMod ("Hclose" with "[-HΦ]").
      { iNext. iExists _. iFrame. }
      iModIntro. wp_run.
      iApply "IH". iFrame. iExists _. iSplit=>//.
    - wp_cas_suc.
      iIntros "Hl'".
      iMod ("Hclose" with "[-HΦ HR]").
      { iNext. iExists true. iFrame. }
      iModIntro. wp_run.
      iDestruct "HR" as "[Ho HR]".
      iApply ("HΦ" with "[-HR]")=>//.
  Qed.

  Lemma release_spec γ R Φ:
    is_lock γ lk R ∗ locked γ ∗ R ∗ Φ void
    ⊢ WP release {{ Φ }}.
  Proof.
    iIntros "(#Hlk & Hlked & HR & HΦ)".
    unfold release.
    iDestruct "Hlk" as (l) "[% ?]". rewrite H.
    iApply wp_atomic.
    { by apply atomic_enf. }
    iInv N as ([]) "[>Hl HR']" "Hclose"; iModIntro.
    - simpl. iApply wp_assign; last iFrame.
      { apply typeof_int8. }
      { constructor. }
      iNext. iIntros "Hl". iMod ("Hclose" with "[-]")=>//.
      iNext. iExists false. iFrame.
    - iDestruct "HR'" as "[>Ho' HR']".
      by iDestruct (locked_exclusive with "Hlked Ho'") as "%".
  Qed.

End spin_lock.
