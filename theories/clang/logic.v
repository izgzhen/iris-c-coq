(* Program Logic *)

Require Export lang.
From iris.base_logic Require Import gen_heap big_op.
From iris.algebra Require Export gmap agree auth.
From iris.base_logic.lib Require Export wsat fancy_updates namespaces.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".
Import uPred.

Class clangG Σ := ClangG {
  clangG_invG :> invG.invG Σ;
  clangG_memG :> gen_heapG block (list byteval) Σ
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

  Definition mapstoval (l: addr) (q: Qp) (v: val) (t: type) : iProp Σ :=
    (∃ bytes bytes',
       mapsto (l.1) q bytes ∗
       ⌜ encode_val t v = bytes' ∧ take (length bytes') (drop (l.2) bytes) = bytes' ⌝)%I.
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

Notation "l ↦{ q } v @ t" := (mapstoval l q v t)
  (at level 20, q at level 50, format "l  ↦{ q }  v  @  t") : uPred_scope.
Notation "l ↦ v @ t" :=
  (mapstoval l 1%Qp v t) (at level 20) : uPred_scope.
Notation "l ↦{ q } -" := (∃ v t, l ↦{q} v @ t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

Section rules.
  Context `{clangG Σ}.

  Lemma wp_unfold E c Φ Φret: WP c @ E {{ Φ; Φret }} ⊣⊢ wp_pre wp E c Φ Φret.
    (* Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed. *)
  Admitted. (* XXX: just too slow ... *)

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

  (* NOTE: it looks not very useful ... *)
  (* Lemma wp_bind_e {E e} (K: list exprctx) Φ Φret: *)
  (*   WP cure e @ E {{ v, WP cure (fill_ectxs (Evalue v) K) {{ Φ ; Φret }} ; Φret }} *)
  (*   ⊢ WP cure (fill_ectxs e K) @ E {{ Φ ; Φret }}. *)

  Lemma wp_lift_step E Φ Φret e1 :
    to_val e1 = None →
    to_ret_val e1 = None →
    (∀ σ1, gen_heap_ctx σ1 ={E,∅}=∗
      ⌜reducible e1 σ1⌝ ∗
      ▷ ∀ e2 σ2, ⌜cstep e1 σ1 e2 σ2⌝ ={∅,E}=∗
        gen_heap_ctx σ2 ∗ WP e2 @ E {{ Φ; Φret }})
    ⊢ WP e1 @ E {{ Φ; Φret }}.
  Proof. iIntros (??) "H". rewrite wp_unfold /wp_pre; auto. Qed.

  Lemma wp_lift_estep E Φ Φret e1 :
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

  Lemma wp_lift_sstep {E Φ Φret} s1 :
    to_val (curs s1) = None → to_ret_val (curs s1) = None →
    (∀ σ1, gen_heap_ctx σ1 ={E}=∗
      ⌜reducible (curs s1) σ1⌝ ∗
      ▷ ∀ s2 σ2, ⌜cstep (curs s1) σ1 s2 σ2⌝ ={E}=∗
        gen_heap_ctx σ2 ∗
        default False (to_val s2) Φ)
    ⊢ WP curs s1 @ E {{ Φ ; Φret }}.
  Proof.
    iIntros (??) "H". iApply (wp_lift_step E _ _ (curs s1))=>//; iIntros (σ1) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iMod (fupd_intro_mask' E ∅) as "Hclose"; first set_solver.
    iModIntro; iNext; iIntros (s2 σ2) "%". iMod "Hclose" as "_".
    iMod ("H" $! s2 σ2 with "[#]") as "($ & H)"=>//.
    destruct (to_val s2) eqn:?; last by iExFalso.
    by iApply wp_value.
  Qed.

  Lemma wp_assign {E l v v'} t Φ Φret:
    typeof t v' →
    ▷ l ↦ v @ t ∗ ▷ (l ↦ v' @ t -∗ Φ Vvoid)
    ⊢ WP curs (Sassign (Evalue (Vptr l)) (Evalue v')) @ E {{ Φ ; Φret }}.
  .

  Lemma wp_assign_offset {E b o off v1 v2 v2'} t1 t2 Φ Φret:
    typeof t2 v2' → sizeof t1 = off →
    ▷ (b, o) ↦ Vpair v1 v2 @ Tprod t1 t2 ∗
    ▷ ((b, o) ↦ Vpair v1 v2' @ Tprod t1 t2 -∗ Φ Vvoid)
    ⊢ WP curs (Sassign (Evalue (Vptr (b, o + off)%nat)) (Evalue v2')) @ E {{ Φ ; Φret }}.
  Admitted.
  
  Lemma wp_seq E s1 s2 Φ Φret:
    WP curs s1 @ E {{ _, WP curs s2 @ E {{ Φ ; Φret }} ; Φret }}
    ⊢ WP curs (Sseq s1 s2) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_unseq E s1 s2 Φ Φret:
    WP curs (Sseq s1 s2) @ E {{ Φ ; Φret }}
    ⊢ WP curs s1 @ E {{ _, WP curs s2 @ E {{ Φ ; Φret }} ; Φret }}.
  Admitted.
  
  Lemma wp_load E Φ p v t q Φret:
    ▷ p ↦{q} v @ t ∗ ▷ (p ↦{q} v @ t -∗ Φ v)
    ⊢ WP cure (Ederef (Evalue (Vptr p))) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_op E op v1 v2 v' Φ Φret:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ WP cure (Ebinop op (Evalue v1) (Evalue v2)) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_ret E v Φ Φret:
    Φret v ⊢ WP curs (Srete (Evalue v)) @ E {{ Φ; Φret }}.
  Admitted.

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
  Admitted.

  Lemma wp_snd v1 v2 Φ Φret:
    ▷ WP cure (Evalue v2) {{ Φ; Φret }}
    ⊢ WP cure (Esnd (Evalue (Vpair v1 v2))) {{ Φ; Φret }}.
  Admitted.

  
  Fixpoint params_match (params: decls) (vs: list val) :=
    match params, vs with
      | (_, t)::params, v::vs => typeof t v ∧ params_match params vs
      | [], [] => True
      | _, _ => False
    end.

  Fixpoint alloc_params (addrs: list (addr * type)) (vs: list val) :=
    (match addrs, vs with
       | (l, t)::params, v::vs => l ↦ v @ t ∗ alloc_params params vs
       | [], [] => True
       | _, _ => False
     end)%I.

  Fixpoint subst_e (x: ident) (es: expr) (e: expr) : expr :=
    match e with
      | Evar x' => if decide (x' = x) then es else e
      | Ebinop op e1 e2 => Ebinop op (subst_e x es e1) (subst_e x es e2)
      | Ederef e => Ederef (subst_e x es e)
      | Eaddrof e => Eaddrof (subst_e x es e)
      | Ecast e t => Ecast (subst_e x es e) t
      | Efst e => Efst (subst_e x es e)
      | Esnd e => Esnd (subst_e x es e)
      | _ => e
    end.
  
  Fixpoint subst_s (x: ident) (es: expr) (s: stmts) : stmts :=
    match s with
      | Sskip => Sskip
      | Sprim p => Sprim p
      | Sassign e1 e2 => Sassign e1 (subst_e x es e2)
      | Sif e s1 s2 => Sif (subst_e x es e) (subst_s x es s1) (subst_s x es s2)
      | Swhile c e s => Swhile (subst_e x es c) (subst_e x es e) (subst_s x es s)
      | Srete e => Srete (subst_e x es e)
      | Sret => Sret
      | Scall f args => Scall f (map (subst_e x es) args)
      | Sseq s1 s2 => Sseq (subst_s x es s1) (subst_s x es s2)
    end.

  Fixpoint substs (m: list (ident * (type * addr))) (s: stmts) : stmts :=
    match m with
      | (i, (_, l))::m => substs m (subst_s i (Ederef (Evalue (Vptr l))) s)
      | [] => s
    end.

  Definition resolve_rhs (e: env) (s: stmts) : stmts :=
    substs (map_to_list e) s.

  Fixpoint resolve_lhs_e (ev: env) (e: expr) : option expr :=
    match e with
      | Evar x =>
        (match ev !! x with
           | Some (_, l) => Some (Evalue (Vptr l))
           | None => None
         end)
      | Ederef e' => Ederef <$> resolve_lhs_e ev e'
      | Efst e' => resolve_lhs_e ev e'
      | Esnd e' =>
        (match type_infer ev e', resolve_lhs_e ev e' with
           | Some (Tprod t1 _), Some e'' =>
             Some (Ebinop oplus e'' (Evalue (Vint8 (Byte.repr (sizeof t1)))))
           | _, _ => None
         end)
      | Ecast e' _ => resolve_lhs_e ev e' (* XXX *)
      | Evalue (Vptr l) => Some e
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
      | _ => Some s
    end.

  Fixpoint add_params_to_env (e: env) (params: list (ident * type)) ls : env :=
    match params, ls with
      | (x, t)::ps, l::ls' => add_params_to_env (<[ x := (t, l) ]> e) ps ls'
      | _, _ => e
    end.

  Definition instantiate_f_body (ev: env) (s: stmts) : option stmts :=
    resolve_lhs ev (resolve_rhs ev s).
  
  Lemma wp_call (p: program) es vs params f_body f retty Φ Φret:
    p f = Some (retty, params, f_body) →
    es = map Evalue vs →
    params_match params vs →
    (∀ ls f_body',
       ⌜ length ls = length vs ∧
         instantiate_f_body (add_params_to_env ∅ params ls) f_body = Some f_body' ⌝ -∗
       alloc_params (zip ls (params.*2)) vs -∗
       WP curs f_body' {{ _, True; Φ }})
    ⊢ WP curs (Scall f es) {{ Φ; Φret }}.
  Admitted.

End rules.
