From iris_c.clang Require Import logic notations tactics.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.base_logic.lib Require Export namespaces invariants.
From iris.proofmode Require Import tactics.

(* Spin lock *)

Class lockG Σ := LockG { lock_tokG :> inG Σ (exclR unitC) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitC)].

Section spin_lock.
  
  Definition acquire (lk: expr) : expr :=
    while: (ECAS tybool lk vfalse vtrue == vfalse ) ( void ) ;;
    return: void.

  Definition newlock : expr :=
    return: Ealloc tybool vfalse.

  Definition release (lk: expr) : expr :=
    lk <- vfalse.

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
    iModIntro. iApply ("HΦ" with "[-Hs]")=>//. iExists l. iSplit=>//.
    iPureIntro. split=>//. constructor.
  Qed.

  Definition lkx: ident := 1.

  Lemma newlock_spec (R: iProp Σ) f Φ k ks:
    text_interp f (Function (Tptr tybool) [] newlock) ∗
    R ∗ own_stack ks ∗ (∀ γ lk, own_stack ks -∗ is_lock γ lk R -∗ WP fill_ectxs lk k {{ Φ }})
    ⊢ WP fill_ectxs (Ecall (Tptr tybool) f []) k {{ Φ }}.
  Proof.
    iIntros "(Hf & HR & Hs & HΦ)".
    iApply (wp_call k []); last iFrame; first done.
    iNext. iIntros "Hs'". iApply (newlock_spec' R). iFrame.
    iIntros (??) "Hlk". iIntros "Hs".
    iApply ("HΦ" with "[-Hlk]")=>//.
  Qed.

  Lemma acquire_spec γ R Φ k ks (lk: val) f:
    own_stack ks ∗ text_interp f (Function Tvoid [(lkx, tylock)] (acquire lkx)) ∗
    is_lock γ lk R ∗ (locked γ -∗ R -∗ own_stack ks -∗ WP fill_ectxs void k {{ Φ }})
    ⊢ WP fill_ectxs (Ecall Tvoid f [Evalue lk]) k {{ Φ }}.
  Proof.
    iIntros "(Hs & Hf & #Hlk & HΦ)".
    iApply (wp_call k [lk]); last iFrame; first done.
    iNext. iIntros "Hs'". iDestruct (is_lock_tylock with "Hlk") as "%".
    wp_alloc lkx as "Hlkx". wp_let. wp_load.
    iLöb as "IH".
    unfold acquire.
    iDestruct "Hlk" as (l) "[% ?]". destruct_ands. subst.
    wp_bind (ECAS _ _ _ _).
    iApply wp_atomic.
    { by apply atomic_enf. }
    iInv N as ([]) "[>Hl HR]" "Hclose"; iModIntro.
    - wp_cas_fail.
      iIntros "Hl".
      iMod ("Hclose" with "[-Hs' Hlkx HΦ]").
      { iNext. iExists _. iFrame. }
      iModIntro. wp_run.
      iApply ("IH" with "HΦ Hs' Hlkx").
    - wp_cas_suc.
      iIntros "Hl'".
      iMod ("Hclose" with "[-HΦ Hlkx Hs' HR]").
      { iNext. iExists true. iFrame. }
      iModIntro. wp_run.
      iDestruct "HR" as "[Ho HR]". iFrame.
      iApply ("HΦ" with "[-HR]")=>//.
  Qed.

  Lemma release_spec lk γ R Φ:
    is_lock γ lk R ∗ locked γ ∗ R ∗ Φ void
    ⊢ WP release lk {{ Φ }}.
  Proof.
    iIntros "(#Hlk & Hlked & HR & HΦ)".
    unfold release.
    iDestruct "Hlk" as (l) "[% ?]". destruct_ands. subst.
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
