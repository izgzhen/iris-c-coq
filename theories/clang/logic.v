(* Program Logic *)

From iris.algebra Require Export gmap agree auth frac excl.
From iris.base_logic.lib Require Export wsat fancy_updates namespaces.
From iris_os.clang Require Export lang.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

Instance equiv_type_function: Equiv function := (=).
Instance equiv_type_stack: Equiv stack := (=).

Class clangG Σ := ClangG {
  clangG_invG :> invG.invG Σ;
  clangG_heapG :> gen_heapG addr byteval Σ;
  clangG_textG :> inG Σ (authR (gmapUR ident (agreeR (discreteC function))));
  clangG_textG_name : gname;
  clangG_stackG :> inG Σ (prodR fracR (agreeR (discreteC stack)));
  clangG_stackG_name : gname
}.

Section wp.
  Context `{clangG Σ}.

  Definition text_interp (f: ident) (x: function) :=
    own clangG_textG_name (◯ {[ f := to_agree (x : discreteC function) ]}).

  Definition stack_interp (s: stack) :=
    own clangG_stackG_name ((1/2)%Qp, (to_agree (s: discreteC stack))).

  Definition gen_text (m: text) : iProp Σ :=
    own clangG_textG_name (● (fmap (λ v, to_agree (v : leibnizC _)) m)).

  Definition gen_stack (s: stack) : iProp Σ :=
    own clangG_stackG_name ((1/2)%Qp, (to_agree (s: discreteC stack))).

  Definition state_interp (s: state) (ks: stack) : iProp Σ:=
    (gen_heap_ctx (s_heap s) ∗ gen_text (s_text s) ∗ gen_stack ks)%I.

  Definition wp_pre
           (wp: coPset -c> expr -c> (val -c> iProp Σ) -c> iProp Σ) :
    coPset -c> expr -c> (val -c> iProp Σ) -c> iProp Σ :=
    (λ E cur Φ,
     (∃ v, ⌜ to_val cur = Some v ⌝ ∧ |={E}=> Φ v) ∨
     (⌜ to_val cur = None ⌝ ∧
         (∀ (σ: state) ks,
           state_interp σ ks ={E,∅}=∗ ⌜ reducible cur σ ks ⌝ ∗
            ▷ (∀ cur' σ' ks', ⌜cstep cur σ ks cur' σ' ks'⌝ ={∅,E}=∗
                        state_interp σ' ks' ∗ wp E cur' Φ))))%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof.
    rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
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
    coPset → expr → (val → iProp Σ) → iProp Σ := fixpoint wp_pre.
  Definition wp_aux : { x | x = @wp_def }. by eexists. Qed.
  Definition wp := proj1_sig wp_aux.
  Definition wp_eq : @wp = @wp_def := proj2_sig wp_aux.

End wp.

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

Notation "l ↦{ q } v @ t" := (mapstoval l q v t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  v  @  t") : uPred_scope.
Notation "l ↦ v @ t" :=
  (mapstoval l 1%Qp v t)%I (at level 20) : uPred_scope.
Notation "l ↦{ q } - @ t" := (∃ v, l ↦{q} v @ t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -  @  t") : uPred_scope.
Notation "l ↦ - @ t" := (l ↦{1} - @ t)%I (at level 20) : uPred_scope.

Section rules.
  Context `{clangG Σ}.

  Local Hint Extern 0 (reducible _ _ _) => eexists _, _, _; simpl.

  Local Hint Constructors cstep estep.

  Lemma wp_unfold E c Φ: WP c @ E {{ Φ }} ⊣⊢ wp_pre wp E c Φ.
    (* Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed. *) (* XXX: too slow *)
  Admitted.

  Lemma wp_value Φ E c v:
    to_val c = Some v →
    Φ v ⊢ WP c @ E {{ Φ }}.
  Proof. iIntros (?) "HΦ". rewrite wp_unfold /wp_pre. iLeft. eauto. Qed.

  Lemma wp_strong_mono E1 E2 e Φ Ψ :
    E1 ⊆ E2 → (∀ v, Φ v ={E2}=∗ Ψ v) ∗ WP e @ E1 {{ Φ }} ⊢ WP e @ E2 {{ Ψ }}.
  Proof.
    iIntros (?) "[HΦ H]". iLöb as "IH" forall (e). rewrite !wp_unfold /wp_pre.
    iDestruct "H" as "[Hv|[% H]]"; [iLeft|iRight].
    { iDestruct "Hv" as (v) "[% Hv]". iExists v; iSplit; first done.
      iApply ("HΦ" with ">[-]"). by iApply (fupd_mask_mono E1 _). }
    iSplit; [done|]; iIntros (σ1 ks1) "Hσ".
    iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done.
    iMod ("H" $! _ _ with "Hσ") as "[$ H]".
    iModIntro. iNext. iIntros (e2 σ2 ks2 Hstep).
    iMod ("H" $! _ _ _ with "[#]") as "($ & H)"; auto.
    iMod "Hclose" as "_". by iApply ("IH" with "HΦ").
  Qed.

  Lemma fupd_wp E e Φ : (|={E}=> WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}.
  Proof.
    rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?.
    { iLeft. iExists v; iSplit; first done.
        by iMod "H" as "[H|[% ?]]"; [iDestruct "H" as (v') "[% ?]"|]; simplify_eq. }
      iRight; iSplit; [done|]; iIntros (σ1 ks1) "Hσ1".
    iMod "H" as "[H|[% H]]"; last by iApply "H".
    iDestruct "H" as (v') "[% ?]"; simplify_eq.
  Qed.

  Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}.
  Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed.

  Lemma wp_bind' kes E e Φ :
    ⌜ is_jmp e = false ⌝ ∗
    WP e @ E {{ v, WP (fill_ectxs (Evalue v) kes) @ E {{ Φ }} }} ⊢ WP (fill_ectxs e kes) @ E {{ Φ }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e Φ). rewrite wp_unfold /wp_pre.
    iDestruct "H" as "[% [Hv|[% H]]]".
    { iDestruct "Hv" as (v) "[Hev Hv]"; iDestruct "Hev" as % <-%of_to_val.
        by iApply fupd_wp. }
    rewrite wp_unfold /wp_pre. iRight; iSplit; eauto using fill_ectxs_not_val.
    iIntros (σ1 ks1) "Hσ". iMod ("H" $! _ ks1 with "Hσ") as "[% H]".
    iModIntro; iSplit.
    { iPureIntro. unfold reducible in *.
      destruct H2 as (cur'&σ'&ks'&?). eexists _, _, ks1. apply CSbind=>//.
      assert (ks1 = ks') as ?; first eapply not_jmp_preserves_stack=>//.
      by subst.
    }
    iNext. iIntros (e2 σ2 ks2 Hstep).
    destruct (fill_step_inv e σ1 e2 σ2 kes ks1 ks2) as (e2'&->&?&?); auto; subst.
    iMod ("H" $! e2' σ2 _ with "[%]") as "($ & H)"; eauto.
    iApply "IH". iSplit=>//.
    iPureIntro. eapply cstep_preserves_not_jmp=>//.
  Qed.

  Lemma wp_bind kes E e Φ :
    is_jmp e = false →
    WP e @ E {{ v, WP (fill_ectxs (Evalue v) kes) @ E {{ Φ }} }} ⊢ WP (fill_ectxs e kes) @ E {{ Φ }}.
  Proof. iIntros (?) "?". iApply wp_bind'. iSplit; done. Qed.

  Lemma wp_lift_step E Φ e1 :
    to_val e1 = None →
    (∀ σ1 ks1, state_interp σ1 ks1 ={E,∅}=∗
      ⌜reducible e1 σ1 ks1⌝ ∗
      ▷ ∀ e2 σ2 ks2, ⌜cstep e1 σ1 ks1 e2 σ2 ks2⌝ ={∅,E}=∗
        state_interp σ2 ks2 ∗ WP e2 @ E {{ Φ }})
    ⊢ WP e1 @ E {{ Φ }}.
  Proof. iIntros (?) "H". rewrite wp_unfold /wp_pre; auto. Qed.

  Lemma wp_lift_pure_step E Φ e1 :
    (∀ σ1 ks1, reducible e1 σ1 ks1) →
    (∀ σ1 ks1 σ2 ks2 cur2, cstep e1 σ1 ks1 cur2 σ2 ks2 → σ1 = σ2 ∧ ks1 = ks2) →
    (▷ ∀ cur2 σ1 ks1 σ2 ks2, ⌜ cstep e1 σ1 ks1 cur2 σ2 ks2 ⌝ →
                WP cur2 @ E {{ Φ }})
      ⊢ WP e1 @ E {{ Φ }}.
  Proof.
    iIntros (Hsafe ?) "H".
    iApply wp_lift_step;
      [by eapply reducible_not_val, (Hsafe inhabitant [])|].
    iIntros (σ1 ks1) "Hσ". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit; [done|]; iNext; iIntros (e2 σ2 ? ?).
    iMod "Hclose"; iModIntro.
    destruct (H0 _ _ _ _ _ H1) as [? ?]. subst. iFrame. by iApply "H".
  Qed.

  Lemma stack_agree ks ks':
    stack_interp ks ∗ gen_stack ks' ⊢ ⌜ ks = ks' ⌝.
  Proof.
    iIntros "[Hs' Hs]".
    rewrite /stack_interp /gen_stack.
    iDestruct (own_valid_2 with "Hs Hs'") as "%".
    iPureIntro.
    destruct H0 as [? ?].
    simpl in H1.
    by apply to_agree_comp_valid in H1.
  Qed.

  Lemma stack_pop k k' ks ks':
    stack_interp (k::ks) ∗ gen_stack (k'::ks') ==∗ stack_interp (ks) ∗ gen_stack (ks') ∗ ⌜ k = k' ∧ ks = ks' ⌝.
  Proof.
    iIntros "[Hs Hs']".
    iDestruct (stack_agree with "[-]") as "%"; first iFrame.
    inversion H0. subst.
    rewrite /stack_interp /gen_stack.
    iMod (own_update_2 with "Hs Hs'") as "[Hs Hs']"; last by iFrame.
    rewrite pair_op frac_op' Qp_div_2.
    apply cmra_update_exclusive.
    split; simpl.
    - by rewrite frac_op'.
    - by apply to_agree_comp_valid.
  Qed.

  Lemma stack_push k k' ks ks':
    stack_interp (ks) ∗ gen_stack (ks') ==∗ stack_interp (k::ks) ∗ gen_stack (k'::ks') ∗ ⌜ k = k' ∧ ks = ks' ⌝.
  Admitted.

  Lemma wp_ret k k' ks v Φ:
    stack_interp (k'::ks)  ∗
    (stack_interp ks -∗ WP fill_ectxs (Evalue v) k' {{ Φ }})
    ⊢ WP fill_ectxs (Erete (Evalue v)) k {{ Φ }}.
  Proof.
    iIntros "[Hs HΦ]". iApply wp_lift_step; eauto; first by apply fill_ectxs_not_val.
    iIntros (??) "[Hσ [HΓ Hstk]]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit.
    { iDestruct (stack_agree with "[Hstk Hs]") as "%"; first iFrame.
      subst. iPureIntro. eexists _, _, _. apply CSjstep. constructor.
      apply cont_uninj. done. }
    iNext. iIntros (????).
    inversion H0.
    { simplify_eq.
      assert (enf (Erete (Evalue v)) = true) as ?; first done.
      destruct (fill_estep_inv _ _ _ _ _ H2 H1) as [? [? ?]].
      inversion H3. simplify_eq.
      exfalso. by eapply (escape_false H7 H5).
    }
    simplify_eq. inversion H1.
    - simplify_eq.
      assert (Erete (Evalue v0) = Erete (Evalue v) ∧ k'0 = k) as (?&?).
      { apply cont_inj=>//. }
      inversion H3. subst. iMod (stack_pop with "[Hstk Hs]") as "(Hstk & Hs & %)"; first iFrame.
      destruct H5; subst.
      iFrame. iMod "Hclose" as "_".
      iModIntro. by iApply "HΦ".
    - simplify_eq.
      apply cont_inj in H2=>//.
      destruct H2 as [? ?]; done.
      simpl. apply forall_is_val.
  Qed.

  Lemma wp_skip E Φ v s:
    ▷ WP s @ E {{ Φ }} ⊢ WP Eseq (Evalue v) s @ E {{ Φ }}.
  Proof.
    iIntros "Φ". iApply wp_lift_pure_step; eauto.
    - inversion 1.
      + inversion H1=>//.
        simplify_eq. inversion H1=>//. simplify_eq.
        exfalso. replace (Eseq (Evalue v) s) with (fill_ectxs (Eseq (Evalue v) s) []) in H2; last done.
        replace (fill_expr (fill_ectxs e kes0) k0)
        with (fill_ectxs e (k0::kes0)) in H2; last done.
        by eapply (escape_false H10 H8).
      + simplify_eq. inversion H1; subst.
        * unfold unfill in H4. rewrite H2 in H4.
          simpl in H4. done.
        * replace (Eseq (Evalue v) s) with (fill_ectxs (Eseq (Evalue v) s) []) in H2 =>//.
          apply cont_inj in H2=>//.
          by destruct H2.
          by apply forall_is_val.
    - iNext. iIntros (????? Hstep).
      inversion Hstep.
      + simplify_eq. inversion H0.
        { simplify_eq. done. }
        { simplify_eq. exfalso. by eapply (escape_false H3 H1). }
      + simplify_eq. inversion H0; subst.
        * simplify_eq. by rewrite /unfill H1 /= in H3.
        * replace (Eseq (Evalue v) s) with (fill_ectxs (Eseq (Evalue v) s) []) in H1 =>//.
          apply cont_inj in H1=>//.
          by destruct H1.
          by apply forall_is_val.
  Qed.

  Lemma wp_seq E e1 e2 Φ:
    is_jmp e1 = false →
    WP e1 @ E {{ v, WP Eseq (Evalue v) e2 @ E {{ Φ }} }} ⊢ WP Eseq e1 e2 @ E {{ Φ }}.
  Proof. iIntros (?) "Hseq". iApply (wp_bind [EKseq e2])=>//. Qed.

  Lemma wp_lift_atomic_step {E Φ} s1 :
    to_val s1 = None →
    (∀ σ1 ks1, state_interp σ1 ks1 ={E}=∗
      ⌜reducible s1 σ1 ks1⌝ ∗
      ▷ ∀ s2 σ2 ks2, ⌜cstep s1 σ1 ks1 s2 σ2 ks2⌝ ={E}=∗
        state_interp σ2 ks2 ∗
        default False (to_val s2) Φ)
    ⊢ WP s1 @ E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply (wp_lift_step E _ s1)=>//; iIntros (σ1 ks1) "Hσ1".
    iMod ("H" $! σ1 ks1 with "Hσ1") as "[$ H]".
    iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iNext; iIntros (s2 σ2 ks2) "%". iMod "Hclose" as "_".
    iMod ("H" $! _ _ _ with "[#]") as "($ & H)"=>//.
    destruct (to_val s2) eqn:?; last by iExFalso.
    by iApply wp_value.
  Qed.

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

  Ltac absurd_jstep :=
    match goal with
      | [ HF: fill_ectxs _ _ = ?E |- _ ] =>
        replace E with (fill_ectxs E []) in HF=>//; apply cont_inj in HF=>//;
              [ by destruct HF | by apply forall_is_val ]
    end.

  Ltac atomic_step H :=
    inversion H; subst;
    [ match goal with
        | [ HE: estep _ _ _ _ |- _ ] =>
          inversion HE; subst;
            [ idtac | exfalso;
                match goal with
                  | [ HF: fill_expr (fill_ectxs ?E _) _ = _, HE2: estep ?E _ _ _ |- _ ] =>
                      by eapply (escape_false HE2 HF)
                end ]
      end
    | match goal with
        | [ HJ : jstep _ _ _ _ _ |- _ ] =>
          inversion HJ; subst;
          [ match goal with
              | [ HU: unfill _ _ , HF: fill_ectxs _ _ = _ |- _ ] =>
                  by rewrite /unfill HF /= in HU
            end
          | absurd_jstep ]
      end
    ].

  Lemma wp_assign {E l v v'} t t' Φ:
    typeof v' t' → assign_type_compatible t t' →
    ▷ l ↦ v @ t ∗ ▷ (l ↦ v' @ t -∗ Φ Vvoid)
    ⊢ WP Eassign (Evalue (Vptr l)) (Evalue v') @ E {{ Φ }}.
  Proof.
    iIntros (??) "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (σ1 ks1) "[Hσ HΓ] !>".
    rewrite /mapstoval. iSplit; first eauto.
    iNext; iIntros (v2 σ2 ks2 Hstep).
    iDestruct "Hl" as "[% Hl]".
    iDestruct (gen_heap_update_bytes _ (encode_val v) _ (encode_val v') with "Hσ Hl") as "H".
    {
      rewrite -(typeof_preserves_size v t)=>//.
      rewrite -(typeof_preserves_size v' t')=>//.
        by apply assign_preserves_size. }
    atomic_step Hstep.
    iMod "H" as "[Hσ' Hv']".
    iModIntro. iFrame. iApply "HΦ".
    iSplit=>//. iPureIntro.
    by apply (assign_preserves_typeof t t').
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

  Instance timeless_mapstobytes q bs p: TimelessP (mapstobytes p q bs)%I.
  Proof.
    generalize bs p.
    induction bs0; destruct p0; first apply _.
    simpl. assert (TimelessP (mapstobytes (b, (n + 1)%nat) q bs0)) as ?; first done.
    apply _.
  Qed.

  Instance timeless_mapstoval p q v t : TimelessP (p ↦{q} v @ t)%I.
  Proof. rewrite /mapstoval. apply _. Qed.

  Lemma wp_load {E} Φ p v t q:
    ▷ p ↦{q} v @ t ∗ ▷ (p ↦{q} v @ t -∗ Φ v)
    ⊢ WP Ederef_typed t (Evalue (Vptr p)) @ E {{ Φ }}.
  Proof.
    iIntros "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (σ1 ks1) "[Hσ [HΓ Hs]]".
    unfold mapstoval.
    iDestruct "Hl" as "[>% >Hl]".
    iDestruct (mapsto_readbytes with "[Hσ Hl]") as "%"; first iFrame.
    iModIntro. iSplit; first eauto.
    iNext; iIntros (s2 σ2 ks2 Hstep). iModIntro.
    atomic_step Hstep.
    simpl. iFrame.
    rewrite (same_type_encode_inj (s_heap σ2) t v v0 p)=>//.
    iApply ("HΦ" with "[-]") ; first by iSplit=>//.
  Qed.

  Lemma wp_op E op v1 v2 v' Φ:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ WP Ebinop op (Evalue v1) (Evalue v2) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    iApply wp_lift_pure_step; first eauto.
    { intros. atomic_step H1=>//. }
    iNext. iIntros (??????).
    atomic_step H1.
    rewrite H0 in H9. inversion H9. subst.
    iApply wp_value=>//.
  Qed.

  Lemma wp_while_true cond s Φ:
    ▷ WP Eseq s (Ewhile cond cond s) {{ Φ }}
    ⊢ WP Ewhile cond (Evalue vtrue) s {{ Φ }}.
  Proof.
    iIntros "Hnext".
    iApply wp_lift_pure_step; first eauto.
    { intros. atomic_step H0=>//. }
    iNext. iIntros (??????).
    by atomic_step H0.
  Qed.

  Lemma wp_while_false cond s Φ:
    ▷ Φ Vvoid
    ⊢ WP Ewhile cond (Evalue vfalse) s {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step; first eauto.
    { intros. atomic_step H0=>//. }
    iNext. iIntros (??????).
    atomic_step H0.
    by iApply wp_value.
  Qed.

  Lemma wp_while_inv I Q cond s:
    is_jmp s = false → is_jmp cond = false →
    □ (∀ Φ, (I ∗ (∀ v, ((⌜ v = vfalse ⌝ ∗ Q Vvoid) ∨ (⌜ v = vtrue ⌝ ∗ I)) -∗ Φ v) -∗ WP cond {{ Φ }})) ∗
    □ (∀ Φ, (I ∗ (I -∗ Φ Vvoid)) -∗ WP s {{ Φ }}) ∗ I
    ⊢ WP Ewhile cond cond s {{ Q }}.
  Proof.
    iIntros (??) "(#Hcond & #Hs & HI)".
    iLöb as "IH".
    iApply (wp_bind [EKwhile cond s])=>//.
    iApply "Hcond". iFrame.
    iIntros (v) "[[% HQ]|[% HI]]"; subst.
    - iApply wp_while_false. by iNext.
    - iApply wp_while_true. iNext.
      iApply wp_seq=>//. iApply "Hs". iFrame.
      iIntros "HI". iApply wp_skip.
      iApply "IH". by iNext.
  Qed.

  Lemma wp_fst v1 v2 Φ:
    ▷ Φ v1
    ⊢ WP Efst (Evalue (Vpair v1 v2)) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step; first eauto.
    { intros. atomic_step H0=>//. }
    iNext. iIntros (??????).
    atomic_step H0. by iApply wp_value.
  Qed.

  Lemma wp_snd v1 v2 Φ:
    ▷ Φ v2
    ⊢ WP Esnd (Evalue (Vpair v1 v2)) {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_pure_step; first eauto.
    { intros. atomic_step H0=>//. }
    iNext. iIntros (??????).
    atomic_step H0. by iApply wp_value.
  Qed.

  (* Freshness and memory allocation *)

  Definition fresh_block (σ: heap) : block :=
    let addrst : list addr := elements (dom _ σ : gset addr) in
    let blockset : gset block := foldr (λ l, ({[ l.1 ]} ∪)) ∅ addrst in
    fresh blockset.

  Lemma is_fresh_block σ i: σ !! (fresh_block σ, i) = None.
  Proof.
    assert (∀ (l: addr) ls (X : gset block),
              l ∈ ls → l.1 ∈ foldr (λ l, ({[ l.1 ]} ∪)) X ls) as help.
    { induction 1; set_solver. }
    rewrite /fresh_block /= -not_elem_of_dom -elem_of_elements.
    move=> /(help _ _ ∅) /=. apply is_fresh.
  Qed.

  Lemma alloc_fresh σ Γ ks v t:
    let l := (fresh_block σ, 0)%nat in
    typeof v t →
    estep (Ealloc t (Evalue v)) (State σ Γ ks) (Evalue (Vptr l)) (State (storebytes l (encode_val v) σ) Γ ks).
  Proof.
    intros l ?. apply ESalloc. auto.
    intros o'. apply (is_fresh_block _ o').
  Qed.

  Lemma fresh_store σ1 b o bs:
    ∀ a : nat,
      a > 0 →
      σ1 !! (b, o) = None →
      storebytes (b, (o + a)%nat) bs σ1 !! (b, o) = None.
  Proof.
    induction bs=>//.
    intros. simpl.
    apply lookup_insert_None.
    split. rewrite -Nat.add_assoc.
    apply IHbs=>//. induction a0; crush.
    intros [=]. omega.
  Qed.

  Lemma gen_heap_update_block bs:
    ∀ σ1 b o,
      (∀ o' : offset, σ1 !! (b, o') = None) →
      gen_heap_ctx σ1 ⊢ |==> gen_heap_ctx (storebytes (b, o) bs σ1) ∗ mapstobytes (b, o) 1 bs.
  Proof.
    induction bs.
    - simpl. iIntros (????) "Hσ". eauto.
    - simpl. iIntros (????) "Hσ".
      iMod (IHbs with "Hσ") as "[Hσ' Hbo]"=>//.
      iFrame. iMod (gen_heap_alloc _ (b, o) with "Hσ'") as "[Hσ Hbo]".
      apply fresh_store=>//.
      by iFrame.
  Qed.

  Lemma wp_alloc E v t Φ:
    typeof v t →
    (∀ l, l ↦ v @ t -∗ Φ (Vptr l))
    ⊢ WP Ealloc t (Evalue v) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    iApply wp_lift_atomic_step=>//.
    iIntros ((σ1&Γ) ks1) "[Hσ1 HΓ]".
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _. apply CSestep. by apply alloc_fresh. }
    iNext. iIntros (e2 σ2 ? ?).
    atomic_step H1.
    iMod (gen_heap_update_block with "Hσ1") as "[? ?]"=>//.
    iFrame. iModIntro.
    iApply "HΦ". by iFrame.
  Qed.

  (* Call *)

  Fixpoint alloc_params (addrs: list (type * addr)) (vs: list val) :=
    (match addrs, vs with
       | (t, l)::params, v::vs => l ↦ v @ t ∗ alloc_params params vs
       | [], [] => True
       | _, _ => False
     end)%I.

  Lemma text_singleton_included (σ: text) l v :
    {[l := to_agree v]} ≼ (fmap (λ v, to_agree (v : leibnizC function)) σ) → σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[av []].
    rewrite lookup_fmap fmap_Some_equiv. intros [v' [Hl ->]].
    move=> /Some_included_total /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

  Lemma lookup_text f x Γ:
    text_interp f x ∗ gen_text Γ
    ⊢ ⌜ Γ !! f = Some x⌝.
  Proof.
    iIntros "[Hf HΓ]".
    rewrite /gen_text /text_interp. iDestruct (own_valid_2 with "HΓ Hf")
      as %[Hl %text_singleton_included]%auth_valid_discrete_2.
    done.
  Qed.

  Lemma wp_call k ks es ls params f_body f_body' f retty Φ:
    es = map (fun l => Evalue (Vptr l)) ls →
    instantiate_f_body (add_params_to_env (Env [] []) params ls) f_body = Some f_body' →
    text_interp f (Function retty params f_body) ∗
    stack_interp ks ∗
    ▷ (stack_interp (k::ks) -∗ WP f_body' {{ Φ }})
    ⊢ WP fill_ectxs (Ecall f es) k {{ Φ }}.
  Proof.
    iIntros (??) "[Hf [Hstk HΦ]]".
    iApply wp_lift_step=>//.
    { apply fill_ectxs_not_val. done. }
    iIntros ((σ1&Γ) ks1) "[Hσ1 [HΓ Hs]]". iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iDestruct (lookup_text with "[HΓ Hf]") as "%"; first iFrame=>//.
    simpl in H2.
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _. apply CSjstep. eapply JScall=>//. }
    iNext. iIntros (e2 σ2 ? ?).
    iMod "Hclose". inversion H3; subst.
    - apply fill_estep_inv in H4; last by apply forall_is_val.
      destruct H4 as [? [? ?]]. admit.
    - inversion H4; subst.
      + apply cont_inj in H0=>//; last by apply forall_is_val.
        by destruct H0.
      + apply cont_inj in H0=>//; try apply forall_is_val.
        destruct H0. inversion H0. subst.
        iFrame. iDestruct (stack_agree with "[Hs Hstk]") as "%"; first iFrame.
        subst. iMod (stack_push with "[Hs Hstk]") as "(Hs & Hstk & %)"; first iFrame.
        iFrame. simpl in H6.
        rewrite H6 in H2. inversion H2. subst.
        assert (ls0 = ls) as ?; first admit.
        subst. clear H2 H0.
        rewrite H8 in H1. inversion H1. subst.
        by iApply "HΦ".
  Admitted.

End rules.
