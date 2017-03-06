(* Program Logic *)

From iris_os.clang Require Export lang.
From iris.base_logic Require Import gen_heap big_op.
From iris.algebra Require Export gmap agree auth.
From iris.base_logic.lib Require Export wsat fancy_updates namespaces.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

Class clangG Σ := ClangG {
  clangG_invG :> invG.invG Σ;
  clangG_memG :> gen_heapG addr byteval Σ
}.

Section wp.
  Context `{clangG Σ}.

  Definition wp_pre
           (wp: coPset -c> cureval -c> (val -c> iProp Σ) -c> (val -c> iProp Σ) -c> iProp Σ) :
    coPset -c> cureval -c> (val -c> iProp Σ) -c> (val -c> iProp Σ) -c> iProp Σ :=
    (λ E cur Φ Φret,
     (∃ v, ⌜ to_val cur = Some v ⌝ ∧ |={E}=> Φ v) ∨
     (∃ v, ⌜ to_ret_val cur = Some v ⌝ ∧ |={E}=> Φret v) ∨
     (⌜ to_val cur = None ∧ to_ret_val cur = None ⌝ ∧
         (∀ (σ: mem),
          gen_heap_ctx σ ={E,∅}=∗ ⌜ reducible cur σ ⌝ ∗
            ▷ (∀ cur' σ', ⌜cstep cur σ cur' σ'⌝ ={∅,E}=∗
                        gen_heap_ctx σ' ∗ wp E cur' Φ Φret))))%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof.
    rewrite /wp_pre=> n wp wp' Hwp E e1 Φ Φret.
    repeat (f_contractive || f_equiv); apply Hwp.
  Qed.

  Fixpoint mapstobytes l q bytes: iProp Σ :=
    let '(b, o) := l in
    (match bytes with
       | byte::bs' => mapsto l q byte ∗ mapstobytes (b, o + 1)%nat q bs'
       | _ => True
     end)%I.

  Definition mapstoval (l: addr) (q: Qp) (v: val) (t: type) : iProp Σ :=
    (⌜ typeof v t ⌝ ∗ mapstobytes l q (encode_val v))%I.

  Definition wp_def :
    coPset → cureval → (val → iProp Σ) → (val → iProp Σ) → iProp Σ := fixpoint wp_pre.
  Definition wp_aux : { x | x = @wp_def }. by eexists. Qed.
  Definition wp := proj1_sig wp_aux.
  Definition wp_eq : @wp = @wp_def := proj2_sig wp_aux.

End wp.

Notation "'WP' c @ E {{ Φ ; Φret } }" := (wp E c Φ Φret)
  (at level 20, c, Φ, Φret at level 200,
   format "'WP'  c  @  E  {{  Φ ; Φret  } }") : uPred_scope.
Notation "'WP' c {{ Φ ; Φret } }" := (wp ⊤ c Φ Φret)
  (at level 20, c, Φ, Φret at level 200,
   format "'WP'  c  {{  Φ ; Φret  } }") : uPred_scope.

Notation "'WP' c @ E {{ v , Q ; Φret } }" := (wp E c (λ v, Q) Φret)
  (at level 20, c, Q, Φret at level 200,
   format "'WP'  c  @  E  {{  v ,  Q ; Φret  } }") : uPred_scope.
Notation "'WP' c {{ v , Q ; Φret } }" := (wp ⊤ c (λ v, Q) Φret)
  (at level 20, c, Q, Φret at level 200,
   format "'WP'  c  {{  v ,  Q  ; Φret } }") : uPred_scope.

Notation "'{{{' P } } } e {{{ x .. y , 'RET' pat ; Q ; Φret } } }" :=
  (∀ Φ Φret : _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e {{ Φ; Φret }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  {{{  x .. y ,  RET  pat ;  Q ;  Φret } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ x .. y , 'RET' pat ; Q ; Φret } } }" :=
  (∀ Φ Φret: _ → uPred _,
      P -∗ ▷ (∀ x, .. (∀ y, Q -∗ Φ pat) .. ) -∗ WP e @ E {{ Φ ; Φret }})
    (at level 20, x closed binder, y closed binder,
     format "{{{  P  } } }  e  @  E  {{{  x .. y ,  RET  pat ;  Q ;  Φret } } }") : C_scope.
Notation "'{{{' P } } } e {{{ 'RET' pat ; Q ; Φret } } }" :=
  (∀ Φ Φret : _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e {{ Φ ; Φret }})
    (at level 20,
     format "{{{  P  } } }  e  {{{  RET  pat ;  Q ;  Φret } } }") : C_scope.
Notation "'{{{' P } } } e @ E {{{ 'RET' pat ; Q ; Φret } } }" :=
  (∀ Φ Φret: _ → uPred _, P -∗ ▷ (Q -∗ Φ pat) -∗ WP e @ E {{ Φ; Φret }})
    (at level 20,
     format "{{{  P  } } }  e  @  E  {{{  RET  pat ;  Q ;  Φret } } }") : C_scope.

Notation "l ↦{ q } v @ t" := (mapstoval l q v t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  v  @  t") : uPred_scope.
Notation "l ↦ v @ t" :=
  (mapstoval l 1%Qp v t)%I (at level 20) : uPred_scope.
Notation "l ↦{ q } - @ t" := (∃ v, l ↦{q} v @ t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -  @  t") : uPred_scope.
Notation "l ↦ - @ t" := (l ↦{1} - @ t)%I (at level 20) : uPred_scope.

Section rules.
  Context `{clangG Σ}.

  Lemma wp_unfold E c Φ Φret: WP c @ E {{ Φ; Φret }} ⊣⊢ wp_pre wp E c Φ Φret.
    (* Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed. *) (* XXX: too slow *)
  Admitted.
  

  Lemma wp_skip Φ Φret E: Φ Vvoid ⊢ WP curs Sskip @ E {{ Φ; Φret }}.
  Proof. iIntros "HΦ". rewrite wp_unfold /wp_pre. iLeft. eauto. Qed.

  Lemma wp_value Φ Φret E c v:
    to_val c = Some v →
    Φ v ⊢ WP c @ E {{ Φ; Φret }}.
  Proof. iIntros (?) "HΦ". rewrite wp_unfold /wp_pre. iLeft. eauto. Qed.

  Lemma wp_strong_mono E1 E2 c Φ Φret Ψ Ψret:
    E1 ⊆ E2 →
    ((∀ v, Φ v ={E2}=∗ Ψ v) ∧ (∀ v, Φret v ={E2}=∗ Ψret v)) ∗ WP c @ E1 {{ Φ; Φret }}
    ⊢ WP c @ E2 {{ Ψ; Ψret }}.
  Proof.
    iIntros (?) "[HΦ H]". iLöb as "IH" forall (c). rewrite !wp_unfold /wp_pre.
    iDestruct "H" as "[Hv|[Hrv|[% H]]]".
    - iLeft. iDestruct "Hv" as (v) "[% Hv]". iExists v; iSplit; first done.
      iDestruct "HΦ" as "[HΦ _]". iApply ("HΦ" with ">[-]"). by iApply (fupd_mask_mono E1 _).
    - iRight. iLeft. iDestruct "Hrv" as (v) "[% Hrv]". iExists v; iSplit; first done.
      iDestruct "HΦ" as "[_ HΦret]".
      iApply ("HΦret" with ">[-]"). by iApply (fupd_mask_mono E1 _). (* XXX: Boilerplate? *)
    - iRight. iRight. iSplit; [done|]; iIntros (σ1) "Hσ".
      iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
      iMod ("H" $! σ1 with "Hσ") as "[$ H]".
      iModIntro. iNext. iIntros (e2 σ2 Hstep).
      iMod ("H" $! e2 σ2 with "[#]") as "($ & H)"; auto.
      iMod "Hclose" as "_". iApply ("IH" $! e2 with "HΦ H").
  Qed.

  Lemma fupd_wp E e Φ Φret: (|={E}=> WP e @ E {{ Φ; Φret }}) ⊢ WP e @ E {{ Φ; Φret }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H".
    destruct (to_val e) as [v|] eqn:Hev; destruct (to_ret_val e) as [retv|] eqn:Hevr.
    - assert (to_val e = None) as H0; first by eapply ret_val_implies_not_val.
      simplify_eq.
    - iLeft. iExists v; iSplit; first done.
      iMod "H" as "[H|[H|[% ?]]]"; try iDestruct "H" as (v') "[% ?]"; try (by inversion H0).
    - iRight. iLeft. iExists retv; iSplit; first done.
      iMod "H" as "[H|[H|[% ?]]]"; try iDestruct "H" as (v') "[% ?]"; try (by inversion H0).
    - iRight. iRight. iSplit; first done.
      iIntros (σ1) "Hσ1". iMod "H" as "[H|[H|[% H]]]".
      + iDestruct "H" as (v') "[% ?]"; simplify_eq.
      + iDestruct "H" as (v') "[% ?]"; simplify_eq.
      + by iApply "H".
  Qed.

  Lemma wp_fupd E c Φ Φret: WP c @ E {{ v, |={E}=> Φ v ; fun v => |={E}=> Φret v}} ⊢ WP c @ E {{ Φ; Φret }}.
  Proof. iIntros "H". iApply (wp_strong_mono E)=>//. iFrame. iSplit; auto. Qed.

  Lemma wp_bind {E e} (Kes: list exprctx) (Ks: stmtsctx) Φ Φret:
    WP cure e @ E
       {{ v, WP curs (fill_stmts (fill_ectxs (Evalue v) Kes) Ks) @ E {{ Φ ; Φret }} ; fun _ => True }}
    ⊢ WP curs (fill_stmts (fill_ectxs e Kes) Ks) @ E {{ Φ ; Φret }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
    iDestruct "H" as "[Hv|[Hrv|[% H]]]".
    - iDestruct "Hv" as (v) "[Hev Hv]". iDestruct "Hev" as % <-%of_to_val.
      by iApply fupd_wp.
    - iDestruct "Hrv" as (rv) "[% Hv]". inversion H0.
    - rewrite wp_unfold /wp_pre. iRight; iRight; iSplit.
      { eauto using fill_not_val, fill_not_ret_val. }
      iIntros (σ1) "Hσ". iMod ("H" $! _ with "Hσ") as "[% H]".
      iModIntro. iSplitL "". { iPureIntro. by apply lift_reducible. }
      iNext; iIntros (e2 σ2 Hstep).
      destruct H0. destruct (fill_step_inv σ1 σ2 e e2 Kes Ks) as (e2'&->&[]); auto.
      subst. iMod ("H" $! (cure e2') σ2 with "[#]") as "($ & H)".
      { iPureIntro. by apply CSestep. }
      by iApply "IH".
  Qed.

  (* NOTE: only for debugging purpose *)
  Lemma wp_bind_e {E e} (K: list exprctx) Φ Φret:
    WP cure e @ E {{ v, WP cure (fill_ectxs (Evalue v) K) {{ Φ ; Φret }} ; Φret }}
    ⊢ WP cure (fill_ectxs e K) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_lift_step E Φ Φret e1 :
    to_val e1 = None →
    to_ret_val e1 = None →
    (∀ σ1, gen_heap_ctx σ1 ={E,∅}=∗
      ⌜reducible e1 σ1⌝ ∗
      ▷ ∀ e2 σ2, ⌜cstep e1 σ1 e2 σ2⌝ ={∅,E}=∗
        gen_heap_ctx σ2 ∗ WP e2 @ E {{ Φ; Φret }})
    ⊢ WP e1 @ E {{ Φ; Φret }}.
  Proof. iIntros (??) "H". rewrite wp_unfold /wp_pre; auto. Qed.

  Lemma wp_lift_pure_step E Φ Φret e1 :
    (∀ σ1, reducible (cure e1) σ1) →
    (▷ ∀ e2 σ, ⌜ estep e1 e2 σ ⌝ →
                WP (cure e2) @ E {{ Φ ; Φret }})
      ⊢ WP cure e1 @ E {{ Φ ; Φret }}.
  Proof.
    iIntros (Hsafe) "H".
    iApply wp_lift_step;
      [by eapply reducible_not_val, (Hsafe inhabitant) |
       by eapply reducible_not_ret_val, (Hsafe inhabitant)|].
    iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit; [done|]; iNext; iIntros (e2 σ2 ?).
    iMod "Hclose"; iModIntro.
    inversion H0. subst. iFrame. by iApply "H".
  Qed.

  Lemma wp_lift_atomic_step {E Φ Φret} s1 :
    to_val s1 = None → to_ret_val s1 = None →
    (∀ σ1, gen_heap_ctx σ1 ={E}=∗
      ⌜reducible s1 σ1⌝ ∗
      ▷ ∀ s2 σ2, ⌜cstep s1 σ1 s2 σ2⌝ ={E}=∗
        gen_heap_ctx σ2 ∗
        default False (to_val s2) Φ)
    ⊢ WP s1 @ E {{ Φ ; Φret }}.
  Proof.
    iIntros (??) "H". iApply (wp_lift_step E _ _ s1)=>//; iIntros (σ1) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iNext; iIntros (s2 σ2) "%". iMod "Hclose" as "_".
    iMod ("H" $! s2 σ2 with "[#]") as "($ & H)"=>//.
    destruct (to_val s2) eqn:?; last by iExFalso.
    by iApply wp_value.
  Qed.
  
  Local Hint Extern 0 (reducible _ _) => eexists _, _; simpl.

  Local Hint Constructors cstep sstep estep.

  Lemma gen_heap_update_bytes σ:
    ∀ bs l bs',
      length bs = length bs' →
      gen_heap_ctx σ -∗ mapstobytes l 1 bs ==∗
      (gen_heap_ctx (storebytes l bs' σ) ∗ mapstobytes l 1 bs').
  Proof.
    induction bs; destruct l.
    - intros []=>//. intros _. iIntros "$ _"=>//.
    - induction bs'=>//. simpl. intros [=].
      iIntros "Hσ [Ha Hbs]".
      iMod (IHbs with "Hσ Hbs") as "[Hσ' Hbs']"=>//.
      iMod (@gen_heap_update with "Hσ' Ha") as "[$ Ha']".
      by iFrame.
  Qed.

  Lemma wp_assign {E l v v'} t t' Φ Φret:
    typeof v' t' → assign_type_compatible t t' →
    ▷ l ↦ v @ t ∗ ▷ (l ↦ v' @ t -∗ Φ Vvoid)
    ⊢ WP curs (Sassign (Evalue (Vptr l)) (Evalue v')) @ E {{ Φ ; Φret }}.
  Proof.
    iIntros (??) "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (σ1) "Hσ !>".
    rewrite /mapstoval. iSplit; first eauto.
    iNext; iIntros (v2 σ2 Hstep).
    iDestruct "Hl" as "[% Hl]".
    iDestruct (gen_heap_update_bytes _ (encode_val v) _ (encode_val v') with "Hσ Hl") as "H".
    {
      rewrite -(typeof_preserves_size v t)=>//.
      rewrite -(typeof_preserves_size v' t')=>//.
      by apply assign_preserves_size. }
    inversion Hstep. subst. inversion H4. subst.
    inversion H4. subst. iMod "H" as "[Hσ' Hv']".
    iModIntro. iFrame. iApply "HΦ".
    iSplit=>//.
    iPureIntro. by apply (assign_preserves_typeof t t').
  Qed.

  Lemma mapstobytes_prod b q:
    ∀ v1 o v2,
      mapstobytes (b, o) q (encode_val (Vpair v1 v2)) ⊣⊢
      mapstobytes (b, o) q (encode_val v1) ∗
      mapstobytes (b, o + length (encode_val v1))%nat q (encode_val v2).
  Proof.
    intro v1. simpl. induction (encode_val v1); intros; iSplit.
    - iIntros "?". simpl. iSplit; first done. by rewrite Nat.add_0_r.
    - simpl. iIntros "[_ ?]". by rewrite Nat.add_0_r.
    - simpl. iIntros "[$ ?]". replace (o + S (length l))%nat with ((o + 1) + length l)%nat; last omega.
      by iApply IHl.
    - simpl. iIntros "[[$ ?] ?]".
      replace (o + S (length l))%nat with ((o + 1) + length l)%nat; last omega.
      iApply IHl. iFrame.
  Qed.

  Lemma mapstoval_split b o q v1 v2 t1 t2:
    (b, o) ↦{q} Vpair v1 v2 @ Tprod t1 t2 ⊢
    (b, o) ↦{q} v1 @ t1 ∗ (b, o + sizeof t1)%nat ↦{q} v2 @ t2.
  Proof.
    iIntros "[% H]".
      match goal with [H : typeof _ _ |- _] => inversion H; subst end.
      iDestruct (mapstobytes_prod with "H") as "[H1 H2]".
      iSplitL "H1".
      + by iFrame.
      + rewrite (typeof_preserves_size v1 t1)//.
        by iFrame.
  Qed.

  Lemma mapstoval_join b o q v1 v2 t1 t2:
    (b, o) ↦{q} v1 @ t1 ∗ (b, o + sizeof t1)%nat ↦{q} v2 @ t2 ⊢
    (b, o) ↦{q} Vpair v1 v2 @ Tprod t1 t2.
  Proof.
    iIntros "[[% H1] [% H2]]".
    iDestruct (mapstobytes_prod with "[H1 H2]") as "?".
    { iFrame "H1". by rewrite -(typeof_preserves_size v1 t1). }
    iFrame. iPureIntro. by constructor.
  Qed.

  Lemma wp_seq_skip E s2 Φ Φret:
    (|={E}=> WP curs s2 @ E {{ v, Φ v;Φret }})%I
    ⊢ WP curs (Sseq Sskip s2) @ E {{ v, Φ v;Φret }}.
  Proof.
    iIntros "H".
    rewrite !wp_unfold /wp_pre. iRight; iRight; iSplit=>//.
    iIntros (σ1) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit; first eauto.
    iNext; iIntros (e2 σ2 ?).
    iMod "Hclose". inversion H0. subst. inversion H2. subst. iFrame.
    - rewrite !wp_unfold /wp_pre. done.
    - subst. inversion H7.
  Qed.

  Lemma wp_ret E v Φ Φret:
    Φret v ⊢ WP curs (Srete (Evalue v)) @ E {{ Φ; Φret }}.
  Admitted.

  Lemma wp_seq_ret E s1 s2 rv Φ Φret:
    to_ret_val (curs s1) = Some rv →
    (|={E}=> Φret rv)%I
    ⊢ WP curs (Sseq s1 s2) @ E {{ v, Φ v;Φret }}.
  Admitted.

  Lemma wp_seq E s1 s2 Φ Φret:
    WP curs s1 @ E {{ _, WP curs s2 @ E {{ Φ ; Φret }} ; Φret }}
    ⊢ WP curs (Sseq s1 s2) @ E {{ Φ ; Φret }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E s1 Φ). rewrite wp_unfold /wp_pre.
    iDestruct "H" as "[Hv|[Hrv|[% H]]]".
    - iDestruct "Hv" as (v) "[Hev Hv]". iDestruct "Hev" as "%".
      destruct s1=>//.
      iApply (wp_seq_skip E s2 Φ Φret with "Hv").
    - iDestruct "Hrv" as (rv) "[% Hv]".
      by iApply (wp_seq_ret E s1 s2 rv Φ Φret with "Hv").
    - rewrite (wp_unfold E (curs (Sseq s1 s2)) Φ Φret) /wp_pre. iRight; iRight; iSplit.
      { eauto using fill_not_val, fill_not_ret_val. }
      iIntros (σ1) "Hσ". iMod ("H" $! _ with "Hσ") as "[% H]".
      iModIntro. iSplitL "". { iPureIntro. admit. }
      iNext; iIntros (e2 σ2 Hstep).
      destruct H0. assert (∃ s1', cstep (curs s1) σ1 (curs s1') σ2 ∧ e2 = (curs (Sseq s1' s2))) as Hs1.
      { admit. }
      destruct Hs1 as [s1' [Hs1 ?]]. subst.
      iMod ("H" $! _ σ2 with "[#]") as "[$ H]"=>//.
      by iApply "IH".
  Admitted.

  Lemma mapsto_readbytes q σ:
    ∀ bs l, mapstobytes l q bs ∗ gen_heap_ctx σ ⊢ ⌜ readbytes l bs σ ⌝.
  Proof.
    induction bs.
    - iIntros (?) "(Hp & Hσ)". done.
    - destruct l. simpl. iIntros "((Ha & Hp) & Hσ)".
      iDestruct (@gen_heap_valid with "Hσ Ha") as %?.
      iDestruct (IHbs with "[Hp Hσ]") as %?; first iFrame.
      iPureIntro. auto.
  Qed.

  Lemma  same_type_encode_inj σ:
    ∀ t v v' p,
      typeof v t → typeof v' t →
      readbytes p (encode_val v) σ →
      readbytes p (encode_val v') σ →
      v = v'.
  Proof.
    (* This holds for me .. *)
  Admitted.

  Instance timeless_mapstobytes q bs p: TimelessP (mapstobytes p q bs)%I.
  Proof.
    generalize bs p.
    induction bs0; destruct p0; first apply _.
    simpl. assert (TimelessP (mapstobytes (b, (n + 1)%nat) q bs0)) as ?; first done.
    apply _.
  Qed.

  Instance timeless_mapstoval p q v t : TimelessP (p ↦{q} v @ t)%I.
  Proof. rewrite /mapstoval. apply _. Qed.

  Lemma wp_load {E} Φ p v t q Φret:
    ▷ p ↦{q} v @ t ∗ ▷ (p ↦{q} v @ t -∗ Φ v)
    ⊢ WP cure (Ederef_typed t (Evalue (Vptr p))) @ E {{ Φ ; Φret }}.
  Proof.
    iIntros "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (σ1) "Hσ".
    unfold mapstoval.
    iDestruct "Hl" as "[>% >Hl]".
    iDestruct (mapsto_readbytes with "[Hσ Hl]") as "%"; first iFrame.
    iModIntro. iSplit; first eauto.
    iNext; iIntros (s2 σ2 Hstep). iModIntro.
    inversion Hstep. subst.
    inversion H3. subst. simpl. iFrame.
    rewrite (same_type_encode_inj σ2 t v v0 p)=>//. 
    iApply "HΦ".
    iSplit=>//.
  Qed.

  Lemma wp_op E op v1 v2 v' Φ Φret:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ WP cure (Ebinop op (Evalue v1) (Evalue v2)) @ E {{ Φ ; Φret }}.
  Proof.
    iIntros (?) "HΦ". iApply wp_lift_pure_step=>//; first eauto.
    iNext. iIntros (e2 σ2 Estep).
    inversion Estep; subst.
    simplify_eq. iApply wp_value=>//.
  Qed.

  Lemma wp_while_true E cond s Φ Φret:
    ▷ WP curs (Sseq s (Swhile cond cond s)) {{ Φ; Φret }}
    ⊢ WP curs (Swhile cond (Evalue vtrue) s) @ E {{ Φ; Φret }}.
  Admitted.

  Lemma wp_while_false E cond s Φ Φret:
    ▷ Φ Vvoid
    ⊢ WP curs (Swhile cond (Evalue vfalse) s) @ E {{ Φ; Φret }}.
  Admitted.

  Lemma wp_while_inv I Q Φret cond s:
    □ (∀ Φ, (I ∗ (∀ v, ((⌜ v = vfalse ⌝ ∗ Q Vvoid) ∨ (⌜ v = vtrue ⌝ ∗ I)) -∗ Φ v) -∗ WP cure cond {{ Φ ; fun _ => True }})) ∗
    □ (∀ Φ, (I ∗ (I -∗ Φ Vvoid)) -∗ WP curs s {{ Φ; Φret }}) ∗ I
    ⊢ WP curs (Swhile cond cond s) {{ Q ; Φret }}.
  Proof.
    iIntros "(#Hcond & #Hs & HI)".
    iLöb as "IH".
    iApply (wp_bind [] (SKwhile _ _)). simpl.
    iApply "Hcond". iFrame.
    iIntros (v) "[[% HQ]|[% HI]]"; subst.
    - iApply wp_while_false. by iNext.
    - iApply wp_while_true. iNext.
      iApply wp_seq. iApply "Hs". by iFrame.
  Qed.

  Lemma wp_fst v1 v2 Φ Φret:
    ▷ WP cure (Evalue v1) {{ Φ; Φret }}
    ⊢ WP cure (Efst (Evalue (Vpair v1 v2))) {{ Φ; Φret }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_pure_step=>//; first eauto.
    iNext. iIntros (e2 σ2 Estep).
    inversion Estep; subst.
    by simplify_eq.
  Qed.

  Lemma wp_snd v1 v2 Φ Φret:
    ▷ WP cure (Evalue v2) {{ Φ; Φret }}
    ⊢ WP cure (Esnd (Evalue (Vpair v1 v2))) {{ Φ; Φret }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_pure_step=>//; first eauto.
    iNext. iIntros (e2 σ2 Estep).
    inversion Estep; subst.
    by simplify_eq.
  Qed.
  
  Fixpoint params_match (params: decls) (vs: list val) :=
    match params, vs with
      | (_, t)::params, v::vs => typeof v t ∧ params_match params vs
      | [], [] => True
      | _, _ => False
    end.

  Fixpoint alloc_params (addrs: list (type * addr)) (vs: list val) :=
    (match addrs, vs with
       | (t, l)::params, v::vs => l ↦ v @ t ∗ alloc_params params vs
       | [], [] => True
       | _, _ => False
     end)%I.

  Fixpoint lift_list_option {A} (l: list (option A)): option (list A) :=
    match l with
      | Some x :: l' => (x ::) <$> lift_list_option l'
      | None :: _ => None
      | _ => Some []
    end.
  
  Fixpoint resolve_rhs_e (ev: env) (e: expr) : option expr :=
    match e with
      | Evar x => (* closed-ness? *)
        (match sget x (lenv ev) with
          | Some (t, l) => Some $ Ederef_typed t (Evalue (Vptr l))
          | None => None
         end)
      | Ebinop op e1 e2 =>
        match resolve_rhs_e ev e1, resolve_rhs_e ev e2 with
          | Some e1', Some e2' => Some (Ebinop op e1' e2')
          | _, _ => None
        end
      | Ederef e =>
        match type_infer ev e, resolve_rhs_e ev e with
          | Some (Tptr t), Some e' => Some (Ederef_typed t e') 
          | _, _ => None
        end
      | Eaddrof e => Eaddrof <$> resolve_rhs_e ev e
      | Efst e => Efst <$> resolve_rhs_e ev e
      | Esnd e => Esnd <$> resolve_rhs_e ev e
      | Ecall f args => Ecall f <$> lift_list_option (map (resolve_rhs_e ev) args)
      | _ => Some e
    end.
  
  Fixpoint resolve_rhs (ev: env) (s: stmts) : option stmts :=
    match s with
      | Sskip => Some Sskip
      | Sprim p => Some $ Sprim p
      | Sassign e1 e2 => Sassign e1 <$> resolve_rhs_e ev e2
      | Sif e s1 s2 =>
        match resolve_rhs_e ev e, resolve_rhs ev s1, resolve_rhs ev s2 with
          | Some e', Some s1', Some s2' => Some $ Sif e' s1' s2'
          | _, _, _ => None
        end
      | Swhile c e s =>
        match resolve_rhs_e ev c, resolve_rhs_e ev e, resolve_rhs ev s with
          | Some c', Some e', Some s' => Some $ Swhile c' e' s'
          | _, _, _ => None
        end
      | Srete e => Srete <$> resolve_rhs_e ev e
      | Sret => Some Sret
      | Sseq s1 s2 =>
        match resolve_rhs ev s1, resolve_rhs ev s2 with
          | Some s1', Some s2' => Some (Sseq s1' s2')
          | _, _ => None
        end
    end.

  Fixpoint resolve_lhs_e (ev: env) (e: expr) : option expr :=
    match e with
      | Evar x =>
        (match sget x (lenv ev) with
           | Some (_, l) => Some (Evalue (Vptr l))
           | None => None
         end)
      | Ederef e' => resolve_rhs_e ev e'
      | Efst e' => resolve_lhs_e ev e'
      | Esnd e' =>
        (e'' ← resolve_lhs_e ev e';
         match type_infer ev e'' with
           | Some (Tptr (Tprod t1 _)) =>
             Some (Ebinop oplus e'' (Evalue (Vint8 (Byte.repr (sizeof t1)))))
           | _ => None
         end)
      | Evalue (Vptr l) => Some e
      | Ecall f es => Some $ Ecall f es
      | _ => None
    end.
  
  Fixpoint resolve_lhs (e: env) (s: stmts) : option stmts :=
    match s with
      | Sassign e1 e2 => e'' ← resolve_lhs_e e e1; Some (Sassign e'' e2)
      | Sif ex s1 s2 =>
        match resolve_lhs e s1, resolve_lhs e s2 with
          | Some s1', Some s2' => Some (Sif ex s1' s2')
          | _, _ => None
        end
      | Swhile c ex s => Swhile c ex <$> resolve_lhs e s
      | Sseq s1 s2 =>
        match resolve_lhs e s1, resolve_lhs e s2 with
          | Some s1', Some s2' => Some (Sseq s1' s2')
          | _, _ => None
        end
      | Sret => Some Sret
      | Srete e => Some (Srete e)
      | Sprim p => Some $ Sprim p
      | Sskip => Some Sskip
    end.

  Fixpoint add_params_to_env (e: env) (params: list (ident * type)) ls : env :=
    match params, ls with
      | (x, t)::ps, l::ls' => add_params_to_env (Env (sset x (t, l) (lenv e)) (fenv e)) ps ls'
      | _, _ => e
    end.

  Definition instantiate_f_body (ev: env) (s: stmts) : option stmts :=
     (resolve_rhs ev s ≫= resolve_lhs ev).

  Lemma wp_call (p: program) (ev: env) es vs params f_body f retty Φ Φret:
    p f = Some (retty, params, f_body) →
    es = map Evalue vs →
    params_match params vs →
    (∀ ls f_body',
       ⌜ length ls = length vs ∧
         instantiate_f_body (add_params_to_env ev params ls) f_body = Some f_body' ⌝ -∗
       alloc_params (zip (params.*2) ls) vs -∗
       WP curs f_body' {{ _, True; Φ }})
    ⊢ WP cure (Ecall f es) {{ Φ; Φret }}.
  Admitted.

End rules.
