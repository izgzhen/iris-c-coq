From iris.base_logic.lib Require Export fancy_updates.
From iris_c.program_logic Require Export language.
From iris.base_logic Require Import big_op.
From iris.proofmode Require Import tactics classes.
Set Default Proof Using "Type".
Import uPred.

Class irisG' (Λstate : Type) (Σ : gFunctors) := IrisG {
  iris_invG :> invG Σ;
  state_interp : Λstate → iProp Σ;
}.

Notation irisG Λ Σ := (irisG' (state Λ) Σ).

Definition wp_pre `{irisG Λ Σ}
    (wp : coPset -c> (expr Λ * local_state Λ) -c> (val Λ -c> iProp Σ) -c> iProp Σ) :
    coPset -c> (expr Λ * local_state Λ) -c> (val Λ -c> iProp Σ) -c> iProp Σ := λ E e1 Φ, (
  (* value case *)
  (∃ v, ⌜to_val (e1.1) = Some v⌝ ∧ |={E}=> Φ v) ∨
  (* step case *)
  (⌜to_val (e1.1) = None⌝ ∧ ∀ σ1,
     state_interp σ1 ={E,∅}=∗ ⌜reducible (e1.1) (e1.2) σ1⌝ ∗
     ▷ ∀ e2 σ2 efs, ⌜prim_step (e1.1) (e1.2) σ1 (e2.1) (e2.2) σ2 efs⌝ ={∅,E}=∗
       state_interp σ2 ∗ wp E e2 Φ ∗
       [∗ list] ef ∈ efs, wp ⊤ (ef, init_local Λ) (λ _, True)))%I.

Local Instance wp_pre_contractive `{irisG Λ Σ} : Contractive wp_pre.
Proof.
  rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
  repeat (f_contractive || f_equiv); apply Hwp.
Qed.

Definition wp_def `{irisG Λ Σ} :
  coPset → (expr Λ * local_state Λ) → (val Λ → iProp Σ) → iProp Σ := fixpoint wp_pre.
Definition wp_aux : { x | x = @wp_def }. by eexists. Qed.
Definition wp := proj1_sig wp_aux.
Definition wp_eq : @wp = @wp_def := proj2_sig wp_aux.

Arguments wp {_ _ _} _ _%E _.
Instance: Params (@wp) 5.

Notation "'WP' e @ E {{ Φ } }" := (wp E e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  @  E  {{  Φ  } }") : uPred_scope.
Notation "'WP' e {{ Φ } }" := (wp ⊤ e%E Φ)
  (at level 20, e, Φ at level 200,
   format "'WP'  e  {{  Φ  } }") : uPred_scope.

Notation "'WP' e @ E {{ v , Q } }" := (wp E e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  @  E  {{  v ,  Q  } }") : uPred_scope.
Notation "'WP' e {{ v , Q } }" := (wp ⊤ e%E (λ v, Q))
  (at level 20, e, Q at level 200,
   format "'WP'  e  {{  v ,  Q  } }") : uPred_scope.

(* Texan triples *)
Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,   RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (□ ∀ Φ,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})%I
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : uPred_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (□ ∀ Φ, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})%I
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : uPred_scope.

Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat%V) .. ) -∗ WP e @ E {{ Φ }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q } } }" :=
  (∀ Φ : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat%V) -∗ WP e @ E {{ Φ }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q } } }") : C_scope.

Section wp.
Context `{irisG Λ Σ}.
Implicit Types P : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types v : val Λ.
Implicit Types e : (expr Λ * local_state Λ).

(* Weakest pre *)
Lemma wp_unfold E e Φ : WP e @ E {{ Φ }} ⊣⊢ wp_pre wp E e Φ.
Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

Global Instance wp_ne E e n :
  Proper (pointwise_relation _ (dist n) ==> dist n) (@wp Λ Σ _ E e).
Proof.
  revert e. induction (lt_wf n) as [n _ IH]=> e Φ Ψ HΦ.
  rewrite !wp_unfold /wp_pre.
  (* FIXME: figure out a way to properly automate this proof *)
  (* FIXME: reflexivity, as being called many times by f_equiv and f_contractive
  is very slow here *)
  do 18 (f_contractive || f_equiv). apply IH; first lia.
  intros v. eapply dist_le; eauto with omega.
Qed.
Global Instance wp_proper E e :
  Proper (pointwise_relation _ (≡) ==> (≡)) (@wp Λ Σ _ E e).
Proof.
  by intros Φ Φ' ?; apply equiv_dist=>n; apply wp_ne=>v; apply equiv_dist.
Qed.

Lemma wp_value' E Φ v s : Φ v ⊢ WP (of_val v, s) @ E {{ Φ }}.
Proof.
  iIntros "HΦ". rewrite wp_unfold /wp_pre.
  iLeft; iExists v; rewrite to_of_val; auto.
Qed.

Lemma wp_value_inv E Φ v s : WP (of_val v, s) @ E {{ Φ }} ={E}=∗ Φ v.
Proof.
  rewrite wp_unfold /wp_pre to_of_val. iIntros "[H|[% _]]"; [|done].
  by iDestruct "H" as (v') "[% ?]"; simplify_eq.
Qed.

Lemma wp_strong_mono E1 E2 e Φ Ψ :
  E1 ⊆ E2 → (∀ v, Φ v ={E2}=∗ Ψ v) ∗ WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Ψ }}.
Proof.
  iIntros (?) "[HΦ H]". iLöb as "IH" forall (e). rewrite !wp_unfold /wp_pre.
  iDestruct "H" as "[Hv|[% H]]"; [iLeft|iRight].
  { iDestruct "Hv" as (v) "[% Hv]". iExists v; iSplit; first done.
    iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
  iSplit; [done|]; iIntros (σ1) "Hσ".
  iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
  iMod ("H" $! σ1 with "Hσ") as "[$ H]".
  iModIntro. iNext. iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! _ _ efs with "[#]") as "($ & H & $)"; auto.
  iMod "Hclose" as "_". by iApply ("IH" with "HΦ").
Qed.

Lemma fupd_wp E e Φ : (|={E}=> WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}.
Proof.
  rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val (e.1)) as [v|] eqn:?.
  { iLeft. iExists v; iSplit; first done.
    by iMod "H" as "[H|[% ?]]"; [iDestruct "H" as (v') "[% ?]"|]; simplify_eq. }
  iRight; iSplit; [done|]; iIntros (σ1) "Hσ1".
  iMod "H" as "[H|[% H]]"; last by iApply "H".
  iDestruct "H" as (v') "[% ?]"; simplify_eq.
Qed.
Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}.
Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed.

Lemma wp_atomic E1 E2 e Φ :
  atomic (e.1) →
  (|={E1,E2}=> WP e @ E2 {{ v, |={E2,E1}=> Φ v }}) ⊢ WP e @ E1 {{ Φ }}.
Proof.
  iIntros (Hatomic) "H". destruct e.
  destruct (to_val e) as [v|] eqn:He.
  { apply of_to_val in He as <-. iApply wp_fupd. iApply wp_value'.
    iMod "H". by iMod (wp_value_inv with "H"). }
  setoid_rewrite wp_unfold; rewrite /wp_pre. iRight; iSplit; auto.
  iIntros (σ1) "Hσ". iMod "H" as "[H|[_ H]]".
  { iDestruct "H" as (v') "[% ?]"; simpl in *. simplify_eq. }
  iMod ("H" $! _ with "Hσ") as "[$ H]".
  iModIntro. iNext. iIntros (e2 σ2 efs Hstep).
  iMod ("H" with "* []") as "(Hphy & H & $)"; first done.
  rewrite wp_unfold /wp_pre. iDestruct "H" as "[H|H]".
  - iDestruct "H" as (v) "[% >>?]". iModIntro. iFrame.
    destruct e2. simpl in *.
    rewrite -(of_to_val e0 v) //. by iApply wp_value'.
  - iDestruct "H" as "[_ H]".
    iMod ("H" with "* Hphy") as "[H _]"; first iFrame.
    iDestruct "H" as %(? & ? & ? & ? & ?). exfalso.
    by eapply (Hatomic _ _ _ _ _ _ Hstep).
Qed.

Lemma wp_fupd_step E1 E2 e P Φ :
  to_val (e.1) = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> P) -∗ WP e @ E2 {{ v, P ={E1}=∗ Φ v }} -∗ WP e @ E1 {{ Φ }}.
Proof.
  rewrite !wp_unfold /wp_pre. iIntros (??) "HR [Hv|[_ H]]".
  { iDestruct "Hv" as (v) "[% Hv]"; simplify_eq. }
  iRight; iSplit; [done|]. iIntros (σ1) "Hσ".
  iMod "HR". iMod ("H" $! _ with "Hσ") as "[$ H]"; first iFrame.
  iModIntro; iNext; iIntros (e2 σ2 efs Hstep).
  iMod ("H" $! e2 σ2 efs with "[%]") as "($ & H & $)"; auto=>//.
  iMod "HR". iModIntro. iApply (wp_strong_mono E2); first done.
  iSplitR "H"; last iExact "H". iIntros (v) "H". by iApply "H".
Qed.

(** * Derived rules *)
Lemma wp_mono E e Φ Ψ : (∀ v, Φ v ⊢ Ψ v) → WP e @ E {{ Φ }} ⊢ WP e @ E {{ Ψ }}.
Proof.
  iIntros (HΦ) "H"; iApply (wp_strong_mono E E); auto.
  iFrame. iIntros (v) "?". by iApply HΦ.
Qed.
Lemma wp_mask_mono E1 E2 e Φ : E1 ⊆ E2 → WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Φ }}.
Proof. iIntros (?) "H"; iApply (wp_strong_mono E1 E2); auto. iFrame; eauto. Qed.
Global Instance wp_mono' E e :
  Proper (pointwise_relation _ (⊢) ==> (⊢)) (@wp Λ Σ _ E e).
Proof. by intros Φ Φ' ?; apply wp_mono. Qed.

Lemma wp_value E Φ e v : to_val (e.1) = Some v → Φ v ⊢ WP e @ E {{ Φ }}.
Proof. intros. destruct e. rewrite -(of_to_val e v) //; by apply wp_value'. Qed.
Lemma wp_value_fupd' E Φ v s : (|={E}=> Φ v) ⊢ WP (of_val v, s) @ E {{ Φ }}.
Proof. intros. by rewrite -wp_fupd -wp_value'. Qed.
Lemma wp_value_fupd E Φ e v :
  to_val (e.1) = Some v → (|={E}=> Φ v) ⊢ WP e @ E {{ Φ }}.
Proof. intros. rewrite -wp_fupd -wp_value //. Qed.

Lemma wp_frame_l E e Φ R : R ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, R ∗ Φ v }}.
Proof. iIntros "[??]". iApply (wp_strong_mono E E _ Φ); try iFrame; eauto. Qed.
Lemma wp_frame_r E e Φ R : WP e @ E {{ Φ }} ∗ R ⊢ WP e @ E {{ v, Φ v ∗ R }}.
Proof. iIntros "[??]". iApply (wp_strong_mono E E _ Φ); try iFrame; eauto. Qed.

Lemma wp_frame_step_l E1 E2 e Φ R :
  to_val (e.1) = None → E2 ⊆ E1 →
  (|={E1,E2}▷=> R) ∗ WP e @ E2 {{ Φ }} ⊢ WP e @ E1 {{ v, R ∗ Φ v }}.
Proof.
  iIntros (??) "[Hu Hwp]". iApply (wp_fupd_step with "Hu"); try done.
  iApply (wp_mono with "Hwp"). by iIntros (?) "$$".
Qed.
Lemma wp_frame_step_r E1 E2 e Φ R :
  to_val (e.1) = None → E2 ⊆ E1 →
  WP e @ E2 {{ Φ }} ∗ (|={E1,E2}▷=> R) ⊢ WP e @ E1 {{ v, Φ v ∗ R }}.
Proof.
  rewrite [(WP _ @ _ {{ _ }} ∗ _)%I]comm; setoid_rewrite (comm _ _ R).
  apply wp_frame_step_l.
Qed.
Lemma wp_frame_step_l' E e Φ R :
  to_val (e.1) = None → ▷ R ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ v, R ∗ Φ v }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_l E E); try iFrame; eauto. Qed.
Lemma wp_frame_step_r' E e Φ R :
  to_val (e.1) = None → WP e @ E {{ Φ }} ∗ ▷ R ⊢ WP e @ E {{ v, Φ v ∗ R }}.
Proof. iIntros (?) "[??]". iApply (wp_frame_step_r E E); try iFrame; eauto. Qed.

Lemma wp_wand E e Φ Ψ :
  WP e @ E {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ E {{ Ψ }}.
Proof.
  iIntros "Hwp H". iApply (wp_strong_mono E); auto.
  iFrame "Hwp". iIntros (?) "?". by iApply "H".
Qed.
Lemma wp_wand_l E e Φ Ψ :
  (∀ v, Φ v -∗ Ψ v) ∗ WP e @ E {{ Φ }} ⊢ WP e @ E {{ Ψ }}.
Proof. iIntros "[H Hwp]". iApply (wp_wand with "Hwp H"). Qed.
Lemma wp_wand_r E e Φ Ψ :
  WP e @ E {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ WP e @ E {{ Ψ }}.
Proof. iIntros "[Hwp H]". iApply (wp_wand with "Hwp H"). Qed.
End wp.

(** Proofmode class instances *)
Section proofmode_classes.
  Context `{irisG Λ Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val Λ → iProp Σ.

  Global Instance frame_wp p E e R Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) → Frame p R (WP e @ E {{ Φ }}) (WP e @ E {{ Ψ }}).
  Proof. rewrite /Frame=> HR. rewrite wp_frame_l. apply wp_mono, HR. Qed.

  Global Instance is_except_0_wp E e Φ : IsExcept0 (WP e @ E {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_wp -except_0_fupd -fupd_intro. Qed.

  Global Instance elim_modal_bupd_wp E e P Φ :
    ElimModal (|==> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof. by rewrite /ElimModal (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wp. Qed.

  Global Instance elim_modal_fupd_wp E e P Φ :
    ElimModal (|={E}=> P) P (WP e @ E {{ Φ }}) (WP e @ E {{ Φ }}).
  Proof. by rewrite /ElimModal fupd_frame_r wand_elim_r fupd_wp. Qed.

  (* lower precedence, if possible, it should always pick elim_upd_fupd_wp *)
  Global Instance elim_modal_fupd_wp_atomic E1 E2 e P Φ :
    atomic (e.1) →
    ElimModal (|={E1,E2}=> P) P
            (WP e @ E1 {{ Φ }}) (WP e @ E2 {{ v, |={E2,E1}=> Φ v }})%I | 100.
  Proof. intros. by rewrite /ElimModal fupd_frame_r wand_elim_r wp_atomic. Qed.

End proofmode_classes.

Hint Extern 0 (atomic _) => assumption : typeclass_instances.
