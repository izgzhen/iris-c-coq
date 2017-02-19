Require Import lang.
From iris.base_logic Require Import gen_heap.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class clangG Σ := ClangG {
  clangG_invG :> invG.invG Σ;
  clangG_memG :> gen_heapG block (list byteval) Σ
}.

Section definitions.
  Context `{clangG Σ}.
  
  Definition wp_pre
           (wp: coPset -c> code -c> (val -c> iProp Σ) -c> iProp Σ) :
    coPset -c> code -c> (val -c> iProp Σ) -c> iProp Σ :=
    (λ E c Φ,
     (* value case *)
     (∃ v, ⌜to_val c = Some v⌝ ∧ |={E}=> Φ v) ∨
     (* step case *)
     (⌜to_val c = None⌝ ∧
      (∀ (σ: mem),
         gen_heap_ctx σ ={E,∅}=∗
           ⌜reducible c⌝ ∗
           ▷ (∀ c' σ', ⌜head_step c σ c' σ'⌝ ={∅,E}=∗
             gen_heap_ctx σ' ∗ wp E c' Φ))))%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof.
    rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
    repeat (f_contractive || f_equiv); apply Hwp.
  Qed.

  Definition wp_def :
    coPset → code → (val → iProp Σ) → iProp Σ := fixpoint wp_pre.
  Definition wp_aux : { x | x = @wp_def }. by eexists. Qed.
  Definition wp := proj1_sig wp_aux.
  Definition wp_eq : @wp = @wp_def := proj2_sig wp_aux.

  Notation "'WP' c @ E {{ Φ } }" := (wp E c Φ)
    (at level 20, c, Φ at level 200,
     format "'WP'  c  @  E  {{  Φ  } }") : uPred_scope.
  Notation "'WP' c {{ Φ } }" := (wp ⊤ c Φ)
    (at level 20, c, Φ at level 200,
     format "'WP'  c  {{  Φ  } }") : uPred_scope.

  Notation "'WP' c @ E {{ v , Q } }" := (wp E c (λ v, Q))
    (at level 20, c, Q at level 200,
     format "'WP'  c  @  E  {{  v ,  Q  } }") : uPred_scope.
  Notation "'WP' c {{ v , Q } }" := (wp ⊤ c (λ v, Q))
    (at level 20, c, Q at level 200,
     format "'WP'  c  {{  v ,  Q  } }") : uPred_scope.

  Lemma wp_unfold E c Φ : WP c @ E {{ Φ }} ⊣⊢ wp_pre wp E c Φ.
  Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

  Lemma wp_value Φ v E: Φ v ⊢ WP (of_val v) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_unfold /wp_pre.
    iLeft. iExists v. auto.
  Qed.


  Lemma wp_strong_mono E1 E2 c Φ Ψ :
    E1 ⊆ E2 → (∀ v, Φ v ={E2}=∗ Ψ v) ∗ WP c @ E1 {{ Φ }} ⊢ WP c @ E2 {{ Ψ }}.
  Proof.
    iIntros (?) "[HΦ H]". iLöb as "IH" forall (c).
    rewrite !wp_unfold /wp_pre.
    iDestruct "H" as "[Hv|[% H]]"; [iLeft|iRight].
    { iDestruct "Hv" as (v) "[% Hv]". iExists v; iSplit; first done.
      iApply ("HΦ" with ">[-]"). by iApply (fupd_mask_mono E1 _). }
    iSplit; [done|]; iIntros (σ1) "Hσ".
    iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
    iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iNext. iIntros (e2 σ2 Hstep).
    iMod ("H" $! e2 σ2 with "[#]") as "($ & H)"; auto.
    iMod "Hclose" as "_". by iApply ("IH" with "HΦ").
  Qed.

  Lemma fupd_wp E e Φ : (|={E}=> WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
    { iLeft. iExists v; iSplit; first done.
        by iMod "H" as "[H|[% ?]]"; [iDestruct "H" as (v') "[% ?]"|]; simplify_eq. }
      iRight; iSplit; [done|]; iIntros (σ1) "Hσ1".
    iMod "H" as "[H|[% H]]"; last by iApply "H".
    iDestruct "H" as (v') "[% ?]"; simplify_eq.
  Qed.
  Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}.
  Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed.

  Lemma fill_step_inv K e1' σ1 e2 σ2 :
    to_val (e1', knil) = None → head_step (e1', K) σ1 e2 σ2 →
    ∃ e2', e2 = (e2', K) ∧ head_step (e1', knil) σ1 (e2', knil) σ2.
  Admitted.

  Lemma wp_contΦ E k s Φ:
    WP (curs s, knil) @ E {{ v, WP (curs Sskip, k) @ E {{ Φ }} }}
       ⊢ WP (curs s, k) @ E {{ Φ }}.
  Admitted.

  Lemma wp_conte E k e Φ:
    WP (cure e, knil) @ E {{ v, WP (cure (Evalue v), k) @ E {{ Φ }} }}
       ⊢ WP (cure e, k) @ E {{ Φ }}.
  Admitted.

  Lemma wp_bind e Ke ke ks E Φ:
    WP (cure e, (Ke::ke, ks)) @ E {{ Φ }}
       ⊢ WP (cure (fill_expr Ke e), (ke, ks)) @ E {{ Φ }}.
  Admitted.

  Lemma wp_bind_s e Ks ks E Φ:
    WP (cure e, ([], Ks::ks)) @ E {{ Φ }}
       ⊢ WP (curs (fill_stmts Ks e), ([], ks)) @ E {{ Φ }}.
  Admitted.

End definitions.

Definition spec_state := nat. (* XXX: should be parameterized *)

Definition spec_rel := spec_state → (option val * spec_state) → Prop.

Inductive spec_code :=
| SCrel : spec_rel → spec_code.
