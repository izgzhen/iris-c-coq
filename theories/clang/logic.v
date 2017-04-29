(* Program Logic *)

From iris.algebra Require Export gmap agree auth frac excl.
From iris.base_logic.lib Require Export wsat fancy_updates namespaces.
From iris_c.program_logic Require Export weakestpre.
From iris_c.clang Require Export lang.
From iris_c.lib Require Import pair.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

Instance equiv_type_function: Equiv function := (=).
Instance equiv_type_stack: Equiv stack := (=).

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
    destruct e2 as [e2 l2].
    edestruct (fill_step_inv e σ1 e2 σ2 s l2 kes) as (e2'&->&?&?); auto; subst=>//.
    iMod ("H" $! (e2', l2) _ _ with "[%]") as "($ & H & Hefs)"; eauto.
    iFrame "Hefs". iApply "IH". iSplit=>//.
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
        state_interp σ2 ∗ WP e2 @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP (ef, []) {{ _, True }})
    ⊢ WP e1 @ E {{ Φ }}.
  Proof. iIntros (?) "H". rewrite wp_unfold /wp_pre; auto. Qed.

  Lemma wp_lift_pure_step E Φ e1 l1 :
    (∀ σ1, reducible e1 l1 σ1) →
    (∀ σ1 σ2 cur2 l1 l2 efs, cstep e1 l1 σ1 cur2 l2 σ2 efs → σ1 = σ2 ∧ l1 = l2) →
    (▷ ∀ e2 l2 σ1 σ2 efs, ⌜ cstep e1 l1 σ1 e2 l2 σ2 efs ⌝ →
                          WP (e2, l2) @ E {{ Φ }} ∗ [∗ list] ef ∈ efs, WP (ef, []) {{ _, True }})
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

  Lemma wp_ret k k' ks v E Φ:
    WP (fill_ectxs (Evalue v) k', ks) @ E {{ Φ }}
    ⊢ WP (fill_ectxs (Erete (Evalue v)) k, k'::ks) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ".
    iApply wp_lift_step; eauto; first by apply fill_ectxs_not_val.
    iIntros (σ) "[Hσ HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iModIntro. iSplit.
    { iPureIntro. destruct σ. simpl. eexists _, _, (State s_heap s_text), _.
      apply CSjstep. simpl in *. subst. constructor.
      apply cont_uninj. auto. }
    iNext. iIntros (e2 σ2 efs Hcs).
    inversion_cstep_as Hes Hjs; subst.
    { destruct e2. simpl in *. by apply fill_estep_false in Hes. }
    destruct e2. simpl in *. inversion_jstep_as Heq; subst.
    - apply cont_inj in Heq=>//; auto;
      destruct Heq as [Heq ?]; inversion Heq; subst.
      iFrame. by rewrite big_sepL_nil.
    - fill_enf_neq.
  Qed.

  Lemma eseq_pure v s h e2 h' G efs:
    estep G (Eseq (Evalue v) s) h e2 h' efs → h = h' ∧ efs = [].
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
    - destruct σ1. eexists _, _, _, _. simpl. eauto.
    - intros σ1 σ2 e2 l1 l2 efs Hs.
      inversion_cstep_as Hes Hjs=>//.
      + f_equal. simplify_eq. inversion Hes=>//.
        simplify_eq. exfalso.
        rewrite_empty_ctx. simpl in *. escape_false.
      + simplify_eq. inversion Hjs; subst.
        * unfold unfill in H2. rewrite H0 in H2.
          by simpl in *.
        * fill_enf_neq.
    - iNext. iIntros (??????).
      inversion_cstep_as Hes Hjs; subst.
      + inversion Hes; subst.
        { iFrame. by rewrite big_sepL_nil. }
        { escape_false. }
      + simplify_eq. inversion Hjs; subst.
        * by rewrite /unfill H1 /= in H3.
        * fill_enf_neq.
  Qed.

  Lemma wp_seq E e1 e2 l Φ:
    is_jmp e1 = false →
    WP (e1, l) @ E {{ v, WP (Eseq (Evalue v) e2, l) @ E {{ Φ }} }} ⊢ WP (Eseq e1 e2, l) @ E {{ Φ }}.
  Proof. iIntros (?) "Hseq". iApply (wp_bind [EKseq e2])=>//. Qed.

  Lemma wp_lift_atomic_step {E Φ} s1 l1 :
    to_val s1 = None →
    (∀ l1 σ1, state_interp σ1 ={E}=∗
      ⌜reducible s1 l1 σ1⌝ ∗
      ▷ ∀ s2 l2 σ2 efs, ⌜cstep s1 l1 σ1 s2 l2 σ2 efs⌝ ={E}=∗
        state_interp σ2 ∗
        default False (to_val s2) Φ  ∗ [∗ list] ef ∈ efs, WP (ef, []) {{ _, True }})
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
    { iPureIntro. destruct σ1. eexists _, _, _, _. simpl. eauto. }
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
    | [ |- reducible _ _ ?σ ] =>
      destruct σ; eexists _, _, _, _; by repeat constructor
    end.

  Lemma mapsto_typeof q l v t:
    l ↦{q} v @ t ⊢ ⌜ typeof v t ⌝.
  Proof. by iDestruct 1 as "[% ?]". Qed.

  Lemma wp_load {E} ks Φ p v t q:
    ▷ p ↦{q} v @ t ∗ ▷ (p ↦{q} v @ t -∗ Φ v)
    ⊢ WP (Ederef_typed t (Evalue (Vptr p)), ks) @ E {{ Φ }}.
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
    v' ≠ v1 → typeof v1 t → typeof v2 t → (* too strong, should mimick wp_assign *)
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
      destruct σ1. constructor. econstructor=>//. }
    iNext; iIntros (s2 l2 σ2 efs Hstep). iModIntro.
    inversion_cstep_as Hes Hjs; subst.
    - inversion Hes; subst.
      + iFrame. iSplitL; last by rewrite big_sepL_nil.
        iApply ("HΦ" with "[-]"). iSplitR=>//.
      + simpl in *.
        rewrite (same_type_encode_inj h t v' v1 l) in H0=>//.
      + escape_false.
    - absurd_jstep Hjs.
  Qed.

  Lemma wp_cas_suc Φ E ks l t v v2 :
    typeof v t → typeof v2 t → (* too strong, should mimick wp_assign *)
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
    { iPureIntro. destruct σ1. eexists _, _, _, [].
      constructor. apply ESCASSuc=>//. }
    iNext; iIntros (s2 l2 σ2 efs Hstep).
    inversion_cstep_as Hes Hjs; subst.
    - inversion Hes; subst.
      + exfalso. simpl in *.
        rewrite (same_type_encode_inj h' t v vl l) in H17=>//.
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
  Qed.

Ltac atomic_step H :=
  inversion H; subst;
  [ match goal with
    | [ HE: estep _ _ _ _ _ _ |- _ ] =>
      inversion HE; subst;
      [ idtac | exfalso; by escape_false ]
    end
  | match goal with
    | [ HJ : jstep _ _ _ _ _ |- _ ] => absurd_jstep HJ
    end
  ].
  
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

  Lemma wp_while_true cond s Φ ks:
    ▷ WP (Eseq s (Ewhile cond cond s), ks) {{ Φ }}
    ⊢ WP (Ewhile cond (Evalue vtrue) s, ks) {{ Φ }}.
  Proof. iIntros "Hnext". by wp_solve_pure. Qed.

  Lemma wp_while_false cond s ks Φ:
    ▷ Φ Vvoid
    ⊢ WP (Ewhile cond (Evalue vfalse) s, ks) {{ Φ }}.
  Proof. iIntros "HΦ". wp_solve_pure. iApply wp_value=>//. Qed.

  Lemma wp_while_inv I Q cond s ks:
    is_jmp s = false → is_jmp cond = false →
    □ (∀ Φ, (I ∗ (∀ v, ((⌜ v = vfalse ⌝ ∗ Q Vvoid) ∨ (⌜ v = vtrue ⌝ ∗ I)) -∗ Φ v) -∗ WP (cond, ks) {{ Φ }})) ∗
    □ (∀ Φ, (I ∗ (I -∗ Φ Vvoid)) -∗ WP (s, ks) {{ Φ }}) ∗ I
    ⊢ WP (Ewhile cond cond s, ks) {{ Q }}.
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

  Lemma alloc_fresh σ v t G:
    let l := (fresh_block σ, 0)%nat in
    typeof v t →
    estep G (Ealloc t (Evalue v)) σ (Evalue (Vptr l)) (storebytes l (encode_val v) σ) [].
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

  Lemma wp_alloc E v t ks Φ:
    typeof v t →
    ▷ (∀ l, l ↦ v @ t -∗ Φ (Vptr l))
    ⊢ WP (Ealloc t (Evalue v), ks) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    iApply wp_lift_atomic_step=>//.
    iIntros (ks1 (σ1&Γ)) "[Hσ1 HΓ]".
    iModIntro. iSplit.
    { iPureIntro. eexists _, _, _, [].
      apply CSestep. by apply alloc_fresh. }
    iNext. iIntros (e2 l2 σ2 efs ?).
    atomic_step H1.
    iMod (gen_heap_update_block with "Hσ1") as "[? ?]"=>//.
    iFrame. iModIntro. iSplitL; last by rewrite big_sepL_nil.
    iApply "HΦ". by iFrame.
  Qed.

  Lemma wp_let E x t v e e' Φ ks:
    instantiate_let x v t e = Some e' →
    ▷ WP (e', ks) @ E {{ Φ }}
    ⊢ WP (Elet t x (Evalue v) e, ks) @ E {{ Φ }}.
  Proof.
    iIntros (?) "HΦ".
    iApply wp_lift_pure_step; first eauto.
    - intros; solve_red.
    - intros ???????Hcs. inversion_cstep_as Hes Hjs.
      + inversion Hes=>//. simplify_eq.
        escape_false.
      + absurd_jstep Hjs.
    - iNext. iIntros (e2 l2 σ1 σ2 efs Hcs). subst.
      inversion_cstep_as Hes Hjs.
      + inversion Hes=>//; simplify_eq=>//.
        * iSplitL; last by rewrite big_sepL_nil. done.
        * escape_false.
      + absurd_jstep Hjs.
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
 
  Lemma wp_fork E t f vs params e e' Φ ks:
    let_params vs params e = Some e' →
    f T↦ Function t params e ∗ ▷ Φ Vvoid ∗ ▷ (WP (e', []) {{ _, True }})
    ⊢ WP (Efork t f (map Evalue vs), ks) @ E {{ Φ }}.
  Proof.
    iIntros (?) "(#Hf & HΦ & He)".
    iApply wp_lift_step=>//.
    iIntros (σ1) "[Hσ1 HΓ]".
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver.
    iDestruct (lookup_text with "[HΓ]") as "%"; first iFrame=>//.
    simpl in *. iModIntro. iSplit.
    { iPureIntro. eexists (Evalue Vvoid), ks, σ1, [e']. simpl.
      destruct σ1. simpl in *. apply CSestep. by econstructor. }
    iNext. iIntros (????Hcs).
    iMod "Hclose". inversion_cstep_as Hes Hjs.
    - iModIntro. iFrame. simpl in *. destruct a. simpl in *.
      inversion Hes=>//; subst.
      + iFrame. iSplitR "He".
        { iApply wp_value=>//. }
        assert (vs0 = vs).
        { eapply map_inj=>//. simpl. by inversion 1. }
        simplify_eq. by rewrite big_sepL_singleton.
      + exfalso. escape_false.
    - absurd_jstep Hjs.
  Qed.
  
  Lemma wp_call {E ks} k vs params e e' f retty Φ:
    let_params vs params e = Some e' →
    f T↦ Function retty params e ∗
    ▷ WP (e', k::ks) @ E {{ Φ }}
    ⊢ WP (fill_ectxs (Ecall retty f (map Evalue vs)) k, ks) @ E {{ Φ }}.
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
    iMod "Hclose". inversion_cstep_as Hes Hjs.
    { apply fill_estep_false in Hes=>//. }
    inversion_jstep_as Heq.
    + fill_enf_neq.
    + apply cont_inj in Heq=>//; auto.
      destruct Heq as [Heq ?]. inversion Heq. subst.
      iFrame. destruct e2. simpl in *. subst.
      assert (vs0 = vs) as ?.
      { eapply map_inj=>//. simpl. by inversion 1. }
      subst. clear Heq. simplify_eq.
      iSplitL; first by iApply "HΦ".
      by rewrite big_sepL_nil.
  Qed.

End rules.

Global Opaque tmapsto.
