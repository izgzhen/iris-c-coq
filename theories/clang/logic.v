(* Program Logic *)

From iris.algebra Require Export gmap agree auth frac excl.
From iris.base_logic.lib Require Export wsat fancy_updates namespaces.
From iris_c.program_logic Require Export weakestpre.
From iris_c.clang Require Export lang.
From iris_c.lib Require Import pair.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

Definition textG := authR (gmapUR ident (agreeR (discreteC function))).

Class clangG Σ := ClangG {
  clangG_invG :> invG Σ;
  clangG_heapG :> gen_heapG addr byteval Σ;
  clangG_textG :> inG Σ textG;
  clangG_textG_name : gname;
}.

Section wp.
  Context `{clangG Σ}.

  Definition tmapsto (f: ident) (x: function) :=
    (□ own clangG_textG_name (◯ {[ f := to_agree (x : discreteC function) ]}))%I.

  Global Instance tmapsto_persistent f x: PersistentP (tmapsto f x).
  Proof. apply _. Qed.
  
  Definition to_gen_text (t: text) :=
    fmap (λ v, to_agree (v : leibnizC function)) t.

  Definition own_text (m: text) : iProp Σ :=
    own clangG_textG_name (● to_gen_text m).

  Definition clang_state_interp (s: state) : iProp Σ:=
    (gen_heap_ctx (s_heap s) ∗ own_text (s_text s))%I.

  Fixpoint mapstobytes l q bytes: iProp Σ :=
    let '(b, o) := l in
    (match bytes with
       | byte::bs' => mapsto l q byte ∗ mapstobytes (b, o + 1)%nat q bs'
       | _ => True
     end)%I.

  Definition mapstoval (l: addr) (q: Qp) (v: val) (t: type) : iProp Σ :=
    (⌜ typeof v t ⌝ ∗ mapstobytes l q (encode_val v))%I.

End wp.

Instance heapG_irisG `{clangG Σ}: irisG clang_lang Σ := {
  iris_invG := clangG_invG;
  state_interp := clang_state_interp;
}.

Global Opaque iris_invG.

Notation "l ↦{ q } v @ t" := (mapstoval l q v t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  v  @  t") : uPred_scope.
Notation "l ↦ v @ t" :=
  (mapstoval l 1%Qp v t)%I (at level 20) : uPred_scope.
Notation "l ↦{ q } - @ t" := (∃ v, l ↦{q} v @ t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -  @  t") : uPred_scope.
Notation "l ↦ - @ t" := (l ↦{1} - @ t)%I (at level 20) : uPred_scope.
Notation "f T↦ F" := (tmapsto f F) (at level 20): uPred_scope.

Section rules.
  Context `{clangG Σ}.

  Global Instance timeless_mapstobytes q bs p: TimelessP (mapstobytes p q bs)%I.
  Proof.
    generalize bs p.
    induction bs0; destruct p0; first apply _.
    simpl.
    assert (TimelessP (mapstobytes (b, (n + 1)%nat) q bs0)) as ?; first done.
    apply _.
  Qed.

  Global Instance timeless_mapstoval p q v t : TimelessP (p ↦{q} v @ t)%I.
  Proof. rewrite /mapstoval. apply _. Qed.

  Lemma wp_bind' kes E e s Φ :
    ⌜ is_jmp e = false ⌝ ∗
    WP (e, s) @ E {{ v, WP (fill_ectxs (Evalue v) kes, s) @ E {{ Φ }} }}
    ⊢ WP (fill_ectxs e kes, s) @ E {{ Φ }}.
  Proof.
    iIntros "H". iLöb as "IH" forall (E e s Φ). rewrite wp_unfold /wp_pre.
    iDestruct "H" as "[% [Hv|[% H]]]".
    { simpl. iDestruct "Hv" as (v) "[Hev Hv]";
        iDestruct "Hev" as % <-%of_to_val.
        by iApply fupd_wp. }
    rewrite wp_unfold /wp_pre.
    iRight; iSplit; eauto using fill_ectxs_not_val.
    iIntros (σ1) "Hσ". iMod ("H" $! _ with "Hσ") as "[% H]".
    iModIntro; iSplit.
    { iPureIntro. unfold reducible in *.
      destruct H2 as (cur'&?&?σ'&efs&?). eexists _, _, _, _.
      apply CSbind=>//. }
    iNext. iIntros (e2 σ2 efs Hstep). simpl in *.
    destruct e2 as [e2 l2]. destruct s as [s1 Ω1].
    destruct l2 as [s2 Ω2].
    edestruct (fill_step_inv e σ1 e2 σ2 s1 s2 kes efs Ω1 Ω2)
      as (e2'&->&?&?); auto; subst=>//.
    { eapply fill_wellformed=>//. by eapply wellformed_cstep. } simpl in *.
    destruct_ands.
    iMod ("H" $! (e2', (s2, Ω2)) _ _ with "[%]") as "($ & H & Hefs)"; eauto.
    iFrame "Hefs". iApply "IH". try iModIntro. iSplit=>//.
    iPureIntro. eapply cstep_preserves_not_jmp=>//.
  Qed.

  Lemma wp_bind kes E e s Φ :
    is_jmp e = false →
    WP (e, s) @ E {{ v, WP (fill_ectxs (Evalue v) kes, s) @ E {{ Φ }} }}
    ⊢ WP (fill_ectxs e kes, s) @ E {{ Φ }}.
  Proof. iIntros (?) "?". iApply wp_bind'. iSplit; done. Qed.

  Definition reducible := @reducible clang_lang.

  Lemma wp_lift_step E Φ e1 :
    to_val (e1.1) = None →
    (∀ σ1, state_interp σ1 ={E,∅}=∗
      ⌜ reducible (e1.1) (e1.2) σ1⌝ ∗
      ▷ ∀ e2 σ2 efs, ⌜cstep (e1.1) (e1.2) σ1 (e2.1) (e2.2) σ2 efs⌝ ={∅,E}=∗
                     state_interp σ2 ∗ WP e2 @ E {{ Φ }} ∗
                     [∗ list] ef ∈ efs, WP (ef, ([], semp)) {{ _, True }})
    ⊢ WP e1 @ E {{ Φ }}.
  Proof. iIntros (?) "H". rewrite wp_unfold /wp_pre; auto. Qed.

  Lemma wp_lift_pure_step E Φ e1 l1 :
    (∀ σ1, reducible e1 l1 σ1) →
    (∀ σ1 σ2 cur2 l1 l2 efs, cstep e1 l1 σ1 cur2 l2 σ2 efs → σ1 = σ2 ∧ l1 = l2) →
    (▷ ∀ e2 l2 σ1 σ2 efs, ⌜ cstep e1 l1 σ1 e2 l2 σ2 efs ⌝ →
                          WP (e2, l2) @ E {{ Φ }} ∗
                          [∗ list] ef ∈ efs, WP (ef, ([], semp)) {{ _, True }})
      ⊢ WP (e1, l1) @ E {{ Φ }}.
  Proof.
    iIntros (Hsafe Hs) "H".
    iApply wp_lift_step.
    { eapply (@reducible_not_val clang_lang), (Hsafe inhabitant). }
    iIntros (σ1) "?". iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit; [done|]; iNext; iIntros (e2 σ2 ? Hsp).
    iMod "Hclose"; iModIntro.
    destruct (Hs _ _ _ _ _ _ Hsp) as [? ?]. subst. iFrame.
    simpl in *. destruct e2. by iApply "H".
  Qed.

  Lemma kcall_map KS k0 k' l ks Ω1 Ω2:
    forallb not_Kcall KS = true →
    KS ++ (Kcall k0 Ω1) :: l = (Kcall k' Ω2) :: ks →
    k0 = k' ∧ ks = l ∧ Ω1 = Ω2.
  Proof.
    destruct KS; simpl; intros; by simplify_eq.
  Qed.

  Lemma kwhile_map KS c e c' e' k k' l ks:
    forallb not_Kwhile KS = true →
    KS ++ Kwhile c e k :: l = Kwhile c' e' k' :: ks →
    k = k' ∧ c = c' ∧ e = e' ∧ ks = l.
  Proof.
    destruct KS; simpl; intros; by simplify_eq.
  Qed.
  
  Lemma wp_ret k k' ks v E Φ Ω1 Ω2:
    WP (fill_ectxs (Evalue v) k', (ks, Ω1)) @ E {{ Φ }}
    ⊢ WP (fill_ectxs (Erete (Evalue v)) k, (Kcall k' Ω1::ks, Ω2)) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_step; eauto; first by apply fill_ectxs_not_val.
    iIntros (σ) "[Hσ HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit.
    { iPureIntro. destruct σ. simpl. eexists _, _, (State s_heap s_text), _.
      apply CSjstep. simpl in *. subst. apply JSrete with (KS:=[])=>//. }
    iNext. iIntros (e2 σ2 efs Hcs).
    inversion_cstep_as Hes Hjs Hws; subst.
    { destruct e2. simpl in *. by apply fill_estep_false in Hes. }
    { destruct e2. simpl in *. inversion_jstep_as Heq; subst.
      - apply cont_inj in Heq=>//; auto;
        destruct Heq as [Heq ?]; inversion Heq; subst.
        iFrame. apply kcall_map in H4=>//. destruct_ands.
        iMod "Hclose". rewrite big_sepL_nil. by iFrame.
      - fill_enf_neq. }
    { destruct e2. simpl in *. apply fill_wstep_false in Hws=>//.  }
  Qed.

  Lemma eseq_pure v s h e2 h' G efs Ω1:
    estep G Ω1 (Eseq (Evalue v) s) h e2 h' efs → h = h' ∧ efs = [].
  Proof.
    intros Hes. f_equal. simplify_eq. inversion Hes =>//.
    simplify_eq. exfalso.
    rewrite_empty_ctx. simpl in *.
    escape_false.
  Qed.

  Lemma wp_skip E Φ v s k:
    ▷ WP (s, k) @ E {{ Φ }} ⊢ WP (Eseq (Evalue v) s, k) @ E {{ Φ }}.
  Proof.
    iIntros "Φ". iApply wp_lift_pure_step; eauto.
    - destruct σ1. eexists _, _, _, _. simpl.
      destruct k. eauto.
    - intros σ1 σ2 e2 l1 l2 efs Hs.
      inversion_cstep_as Hes Hjs Hws=>//.
      + f_equal. simplify_eq. inversion Hes=>//.
        simplify_eq. exfalso.
        rewrite_empty_ctx. simpl in *. escape_false.
      + simplify_eq. absurd_jstep Hjs.
      + simplify_eq. absurd_jstep Hws.
    - iNext. iIntros (?(?&?)????).
      inversion_cstep_as Hes Hjs Hws; subst.
      + inversion Hes; subst.
        { iFrame. by rewrite big_sepL_nil. }
        { escape_false. }
      + simplify_eq. absurd_jstep Hjs.
      + simplify_eq. absurd_jstep Hws.
  Qed.

  Lemma wp_seq E e1 e2 l Φ:
    is_jmp e1 = false →
    WP (e1, l) @ E {{ v, WP (Eseq (Evalue v) e2, l) @ E {{ Φ }} }}
    ⊢ WP (Eseq e1 e2, l) @ E {{ Φ }}.
  Proof. iIntros (?) "Hseq". iApply (wp_bind [EKseq e2])=>//. Qed.

  Lemma wp_lift_atomic_step {E Φ} s1 l1 :
    to_val s1 = None →
    (∀ l1 σ1, state_interp σ1 ={E}=∗
      ⌜reducible s1 l1 σ1⌝ ∗
      ▷ ∀ s2 l2 σ2 efs, ⌜cstep s1 l1 σ1 s2 l2 σ2 efs⌝ ={E}=∗
        state_interp σ2 ∗
        default False (to_val s2) Φ ∗
        [∗ list] ef ∈ efs, WP (ef, ([], semp)) {{ _, True }})
    ⊢ WP (s1, l1) @ E {{ Φ }}.
  Proof.
    iIntros (?) "H". iApply (wp_lift_step E _ (s1, l1))=>//; iIntros (σ1) "Hσ1".
    iMod ("H" $! l1 σ1 with "Hσ1") as "[$ H]"; first iFrame.
    iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iNext; iIntros (s2 σ2 ? ?). iMod "Hclose" as "_".
    iMod ("H" $! _ _ _ _ with "[#]") as "($ & H & ?)"=>//. iFrame.
    destruct (to_val (s2.1)) eqn:?; last by iExFalso.
    iApply wp_value=>//.
  Qed.

  Lemma gen_heap_update_bytes (σ: heap):
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

  Lemma wp_assign {E l v v'} t t' ks Φ:
    typeof v' t' → assign_type_compatible t t' →
    ▷ l ↦ v @ t ∗ ▷ (l ↦ v' @ t -∗ Φ Vvoid)
    ⊢ WP (Eassign (Evalue (Vptr l)) (Evalue v'), ks) @ E {{ Φ }}.
  Proof.
    iIntros (??) "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (l1 σ1) "[Hσ HΓ] !>".
    rewrite /mapstoval. iSplit; first eauto.
    { iPureIntro. destruct σ1. destruct ks. eexists _, _, _, _. simpl.
      destruct l1. eauto. }
    iNext; iIntros (v2 l2 σ2 efs Hstep).
    iDestruct "Hl" as "[% Hl]".
    iDestruct (gen_heap_update_bytes _ (encode_val v)
                                     _ (encode_val v')
               with "Hσ Hl") as "H".
    { rewrite -(typeof_preserves_size v t)=>//.
      rewrite -(typeof_preserves_size v' t')=>//.
      by apply assign_preserves_size. }
    atomic_step Hstep.
    iMod "H" as "[Hσ' Hv']".
    iModIntro. iFrame. iSplitL; last by rewrite big_sepL_nil.
    simpl. iApply "HΦ".
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
    - simpl. iIntros "[$ ?]".
      replace (o + S (length l))%nat with ((o + 1) + length l)%nat; last omega.
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

  Lemma mapsto_readbytes q (σ: heap):
    ∀ bs l, mapstobytes l q bs ∗ gen_heap_ctx σ ⊢ ⌜ readbytes l bs σ ⌝.
  Proof.
    induction bs.
    - iIntros (?) "(Hp & Hσ)". done.
    - destruct l. simpl. iIntros "((Ha & Hp) & Hσ)".
      iDestruct (@gen_heap_valid with "Hσ Ha") as %?.
      iDestruct (IHbs with "[Hp Hσ]") as %?; first iFrame.
      iPureIntro. auto.
  Qed.

  Ltac solve_red :=
    match goal with
    | [ |- reducible _ ?l ?σ ] =>
      destruct σ; destruct l; eexists _, _, _, _; by repeat constructor
    end.

  Lemma mapsto_typeof q l v t:
    l ↦{q} v @ t ⊢ ⌜ typeof v t ⌝.
  Proof. by iDestruct 1 as "[% ?]". Qed.

  Lemma wp_load {E} ks Φ p v t q:
    ▷ p ↦{q} v @ t ∗ ▷ (p ↦{q} v @ t -∗ Φ v)
    ⊢ WP (Ederef t (Evalue (Vptr p)), ks) @ E {{ Φ }}.
  Proof.
    iIntros "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (l1 σ1) "[Hσ HΓ]".
    unfold mapstoval.
    iDestruct "Hl" as "[>% >Hl]".
    iDestruct (mapsto_readbytes with "[Hσ Hl]") as "%"; first iFrame.
    iModIntro. iSplit; first eauto.
    { iPureIntro. solve_red. }
    iNext; iIntros (s2 l2 σ2 efs Hstep). iModIntro.
    atomic_step Hstep.
    simpl. iFrame. iSplitL; last by rewrite big_sepL_nil.
    rewrite (same_type_encode_inj h' t v v0 p)=>//.
    iApply ("HΦ" with "[-]") ; first by iSplit=>//.
  Qed.

  Lemma wp_cas_fail Φ E ks l t q v' v1 v2 :
    v' ≠ v1 → typeof v1 t → typeof v2 t →
    ▷ l ↦{q} v' @ t ∗ ▷ (l ↦{q} v' @ t -∗ Φ vfalse)
    ⊢ WP (ECAS t (Evalue (Vptr l)) (Evalue v1) (Evalue v2), ks) @ E {{ Φ }}.
  Proof.
    iIntros (???) "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (l1 σ1) "[Hσ HΓ]".
    unfold mapstoval.
    iDestruct "Hl" as "[>% >Hl]".
    iDestruct (mapsto_readbytes with "[Hσ Hl]") as "%"; first iFrame.
    iModIntro. iSplit; first eauto.
    { iPureIntro. eexists _, _, σ1, [].
      destruct σ1. destruct l1. constructor. econstructor=>//. }
    iNext; iIntros (s2 l2 σ2 efs Hstep). iModIntro.
    inversion_cstep_as Hes Hjs Hws; subst.
    - inversion Hes; subst.
      + iFrame. iSplitL; last by rewrite big_sepL_nil.
        iApply ("HΦ" with "[-]"). iSplitR=>//.
      + simpl in *.
        rewrite (same_type_encode_inj h t v' v1 l) in H0=>//.
      + escape_false.
    - absurd_jstep Hjs.
    - absurd_jstep Hws.
  Qed.

  Lemma wp_cas_suc Φ E ks l t v v2 :
    typeof v t → typeof v2 t →
    ▷ l ↦ v @ t ∗ ▷ (l ↦ v2 @ t -∗ Φ vtrue)
    ⊢ WP (ECAS t (Evalue (Vptr l)) (Evalue v) (Evalue v2), ks) @ E {{ Φ }}.
  Proof.
    iIntros (??) "[Hl HΦ]".
    iApply wp_lift_atomic_step=>//.
    iIntros (l1 σ1) "[Hσ HΓ]".
    unfold mapstoval.
    iDestruct "Hl" as "[>% >Hl]".
    iDestruct (mapsto_readbytes with "[Hσ Hl]") as "%"; first iFrame.
    iModIntro. iSplit; first eauto.
    { iPureIntro. destruct σ1. destruct l1. eexists _, _, _, [].
      constructor. apply ESCASSuc=>//. }
    iNext; iIntros (s2 l2 σ2 efs Hstep).
    inversion_cstep_as Hes Hjs Hws; subst.
    - inversion Hes; subst.
      + exfalso. simpl in *.
        rewrite (same_type_encode_inj h' t v vl l) in H18=>//.
      + simpl in *. iFrame.
        iMod (gen_heap_update_bytes _ (encode_val v)
                                    _ (encode_val v2)
                   with "Hσ Hl") as "[H ?]".
        { rewrite -(typeof_preserves_size v t)=>//.
          rewrite -(typeof_preserves_size v2 t)=>//. }
        iFrame. iModIntro. iSplitL; last by rewrite big_sepL_nil.
        iApply "HΦ". iSplit=>//.
      + escape_false.
    - absurd_jstep Hjs.
    - absurd_jstep Hws.
  Qed.

  Ltac wp_solve_pure :=
    iApply wp_lift_pure_step;
    [ intros; solve_red |
      intros ???????Hcs; atomic_step Hcs=>// |
      iNext;
      let Hcs := fresh "Hcs" in
      iIntros (??????Hcs);
      atomic_step Hcs; iSplitL; last by rewrite big_sepL_nil ].
  
  Lemma wp_op E ks op v1 v2 v' Φ:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ WP (Ebinop op (Evalue v1) (Evalue v2), ks) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ". wp_solve_pure.
    simplify_eq. subst. iApply wp_value=>//.
  Qed.

  Lemma wp_var E ks Ω x v t Φ:
    sget x Ω = Some (t, v) →
    Φ v ⊢ WP (Evar x, (ks, Ω)) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    iApply wp_lift_pure_step.
    - intros. exists (Evalue v), (ks, Ω), σ1, []. simpl.
      destruct σ1. apply CSestep. eapply ESvar. done.
    - intros ???????Hcs; atomic_step Hcs=>//.
    - iNext;
      let Hcs := fresh "Hcs" in
      iIntros (??????Hcs);
      atomic_step Hcs; iSplitL; last by rewrite big_sepL_nil.
      simplify_eq. subst. iApply wp_value=>//.
  Qed.

  Lemma wp_pair E ks v1 v2 Φ:
    Φ (Vpair v1 v2) ⊢ WP (Epair (Evalue v1) (Evalue v2), ks) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". wp_solve_pure.
    simplify_eq. subst. iApply wp_value=>//.
  Qed.

  Lemma wp_fst v1 v2 Φ ks:
    ▷ Φ v1
    ⊢ WP (Efst (Evalue (Vpair v1 v2)), ks) {{ Φ }}.
  Proof. iIntros "HΦ". wp_solve_pure. iApply wp_value=>//. Qed.

  Lemma wp_snd v1 v2 Φ ks:
    ▷ Φ v2
    ⊢ WP (Esnd (Evalue (Vpair v1 v2)), ks) {{ Φ }}.
  Proof. iIntros "HΦ". wp_solve_pure. iApply wp_value=>//. Qed.

  Lemma wp_if_true e1 e2 Φ ks:
    ▷ WP (e1, ks) {{ Φ }}
    ⊢ WP (Eif (Evalue vtrue) e1 e2, ks) {{ Φ }}.
  Proof. iIntros "HΦ". wp_solve_pure. done. Qed.

  Lemma wp_if_false e1 e2 Φ ks:
    ▷ WP (e2, ks) {{ Φ }}
    ⊢ WP (Eif (Evalue vfalse) e1 e2, ks) {{ Φ }}.
  Proof. iIntros "HΦ". wp_solve_pure. done. Qed.

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

  Lemma alloc_fresh σ v t G Ω:
    let l := (fresh_block σ, 0)%nat in
    typeof v t →
    estep G Ω (Ealloc t (Evalue v)) σ (Evalue (Vptr l))
          (storebytes l (encode_val v) σ) [].
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
      gen_heap_ctx σ1 ⊢
      |==> gen_heap_ctx (storebytes (b, o) bs σ1) ∗
           mapstobytes (b, o) 1 bs.
  Proof.
    induction bs.
    - simpl. iIntros (????) "Hσ". eauto.
    - simpl. iIntros (????) "Hσ".
      iMod (IHbs with "Hσ") as "[Hσ' Hbo]"=>//.
      iFrame. iMod (gen_heap_alloc _ (b, o) with "Hσ'") as "[Hσ Hbo]".
      apply fresh_store=>//.
      by iFrame.
  Qed.

  Lemma wp_alloc E v t ks Φ:
    typeof v t →
    ▷ (∀ l, l ↦ v @ t -∗ Φ (Vptr l))
    ⊢ WP (Ealloc t (Evalue v), ks) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    iApply wp_lift_atomic_step=>//.
    iIntros (ks1 (σ1&Γ)) "[Hσ1 HΓ]".
    iModIntro. iSplit.
    { iPureIntro. destruct ks1. eexists _, _, _, [].
      apply CSestep. by apply alloc_fresh. }
    iNext. iIntros (e2 l2 σ2 efs ?).
    atomic_step H1.
    iMod (gen_heap_update_block with "Hσ1") as "[? ?]"=>//.
    iFrame. iModIntro. iSplitL; last by rewrite big_sepL_nil.
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
    {[l := to_agree v]} ≼ (fmap (λ v, to_agree (v : leibnizC function)) σ) →
    σ !! l = Some v.
  Proof.
    rewrite singleton_included=> -[av []].
    rewrite lookup_fmap fmap_Some_equiv. intros [v' [Hl ->]].
    move=> /Some_included_total /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

  Lemma lookup_text f x Γ:
    f T↦ x ∗ own_text Γ
    ⊢ ⌜ Γ !! f = Some x⌝.
  Proof.
    iIntros "[#Hf HΓ]".
    rewrite /own_text.
    by iDestruct (own_valid_2 with "HΓ Hf")
      as %[Hl %text_singleton_included]%auth_valid_discrete_2.
  Qed.

  Lemma wp_fork E t f e Φ ks:
    f T↦ Function t [] e ∗ ▷ Φ Vvoid ∗ ▷ (WP (e, ([], semp)) {{ _, True }})
    ⊢ WP (Efork t f, ks) @ E {{ Φ }}.
  Proof.
    iIntros "(#Hf & HΦ & He)".
    iApply wp_lift_step=>//.
    iIntros (σ1) "[Hσ1 HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iDestruct (lookup_text with "[HΓ]") as "%"; first iFrame=>//.
    simpl in *. iModIntro. iSplit.
    { iPureIntro. eexists (Evalue Vvoid), ks, σ1, [e]. simpl.
      destruct σ1. simpl in *. destruct ks. apply CSestep. by econstructor. }
    iNext. iIntros ((?&?)???Hcs).
    iMod "Hclose". inversion_cstep_as Hes Hjs Hws.
    - iModIntro. iFrame. simpl in *. simpl in *.
      inversion Hes=>//; subst.
      + iFrame. iSplitR "He".
        { iApply wp_value=>//. }
        simplify_eq. by rewrite big_sepL_singleton.
      + exfalso. escape_false.
    - absurd_jstep Hjs.
    - absurd_jstep Hws.
  Qed.

  Lemma wp_while ks {E c e} k Φ Ω:
    ▷ WP (Eif c (Eseq e Econtinue) Ebreak, (Kwhile c e k::ks, Ω)) @ E {{ Φ }}
    ⊢ WP (fill_ectxs (Ewhile c e) k, (ks, Ω)) @ E {{ Φ }}.
  Proof.
    iIntros "?".
    iApply wp_lift_step=>//.
    { apply fill_ectxs_not_val. done. }
    iIntros (σ1) "[Hσ1 HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    simpl in *. iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, []. destruct σ1. simpl in *.
      apply CSwstep. eapply WSwhile. }
    iNext. iIntros (e2 σ2 efs Hcs).
    iMod "Hclose". inversion_cstep_as Hes Hjs Hws.
    { apply wfill_estep_false in Hes=>//. }
    { apply wfill_jstep_false in Hjs=>//. }
    { inversion_wstep_as Heq.
      + apply cont_inj in Heq=>//; auto.
        destruct Heq as [Heq ?]. inversion Heq. subst.
        iFrame. destruct e2. simpl in *. subst.
        iFrame. by rewrite big_sepL_nil.
      + fill_enf_neq.
      + fill_enf_neq. }
  Qed.

  Lemma wp_break ks {E} k k' c e Φ Ω:
    WP (fill_ectxs (Evalue Vvoid) k', (ks, Ω)) @ E {{ Φ }}
       ⊢ WP (fill_ectxs Ebreak k, (Kwhile c e k'::ks, Ω)) @ E {{ Φ }}.
  Proof.
    iIntros "?".
    iApply wp_lift_step=>//.
    { apply fill_ectxs_not_val. done. }
    iIntros (σ1) "[Hσ1 HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    simpl in *. iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _. destruct σ1. simpl in *.
      apply CSwstep. eapply WSbreak with (KS:=[]). done. }
    iNext. iIntros (e2 σ2 efs Hcs).
    iMod "Hclose". inversion_cstep_as Hes Hjs Hws.
    { apply wfill_estep_false in Hes=>//. }
    { apply wfill_jstep_false in Hjs=>//. }
    { inversion_wstep_as Heq.
      + fill_enf_neq.
      + apply cont_inj in Heq=>//; auto.
        destruct Heq as [Heq ?]. inversion Heq.
        iFrame. destruct e2. simpl in *. subst.
        iFrame. apply kwhile_map in H2=>//.
        destruct_ands. iFrame.
        by rewrite big_sepL_nil.
      + fill_enf_neq. }
  Qed.

  Lemma wp_continue {E} ks {c e} k k' Φ Ω:
    WP (fill_ectxs (Ewhile c e) k', (ks, Ω)) @ E {{ Φ }}
    ⊢ WP (fill_ectxs Econtinue k, (Kwhile c e k'::ks, Ω)) @ E {{ Φ }}.
  Proof.
    iIntros "?".
    iApply wp_lift_step=>//.
    { apply fill_ectxs_not_val. done. }
    iIntros (σ1) "[Hσ1 HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    simpl in *. iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, _. destruct σ1. simpl in *.
      apply CSwstep. eapply WScontinue with (KS:=[]). done. }
    iNext. iIntros (e2 σ2 efs Hcs).
    iMod "Hclose". inversion_cstep_as Hes Hjs Hws.
    { apply wfill_estep_false in Hes=>//. }
    { apply wfill_jstep_false in Hjs=>//. }
    { inversion_wstep_as Heq.
      + fill_enf_neq.
      + fill_enf_neq.
      + apply cont_inj in Heq=>//; auto.
        destruct Heq as [Heq ?]. inversion Heq.
        iFrame. destruct e2. simpl in *. subst.
        iFrame. apply kwhile_map in H2=>//.
        destruct_ands. iFrame.
        by rewrite big_sepL_nil. }
  Qed.

  Lemma wp_call {E ks} Ω Ω' {k} v params e f retty Φ:
    let_params v params = Some Ω →
    f T↦ Function retty params e ∗
    ▷ WP (e, (Kcall k Ω'::ks, Ω)) @ E {{ Φ }}
    ⊢ WP (fill_ectxs (Ecall retty f (Evalue v)) k, (ks, Ω')) @ E {{ Φ }}.
  Proof.
    iIntros (Hls) "[#Hf HΦ]".
    iApply wp_lift_step=>//.
    { apply fill_ectxs_not_val. done. }
    iIntros (σ1) "[Hσ1 HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iDestruct (lookup_text with "[HΓ]") as "%"; first iFrame=>//.
    simpl in *. iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, []. destruct σ1. simpl in *.
      apply CSjstep. eapply JScall=>//. }
    iNext. iIntros (e2 σ2 efs Hcs).
    iMod "Hclose". inversion_cstep_as Hes Hjs Hws.
    { apply fill_estep_false in Hes=>//. }
    { inversion_jstep_as Heq.
      + fill_enf_neq.
      + apply cont_inj in Heq=>//; auto.
        destruct Heq as [Heq ?]. inversion Heq. subst.
        iFrame. destruct e2. simpl in *. subst.
        subst. clear Heq. simplify_eq.
        iSplitL; first by iApply "HΦ".
        by rewrite big_sepL_nil. }
    { apply fill_wstep_false in Hws=>//. }
  Qed.

End rules.

Global Opaque tmapsto.
