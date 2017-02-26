(* Program Logic *)

Require Export lang.
From iris.base_logic Require Import gen_heap big_op.
From iris.algebra Require Export gmap agree auth.
From iris.base_logic.lib Require Export wsat fancy_updates namespaces.
From iris.proofmode Require Import tactics.
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
     match cur with
       | curs Sskip => |={E}=> Φ Vvoid
       | cure (Evalue v) => |={E}=> Φ v
       | curs Sret => |={E}=> Φret Vvoid
       | curs (Srete (Evalue v)) => |={E}=> Φret v
       | _ =>
         (∀ (σ: mem),
          gen_heap_ctx σ ={E,∅}=∗
            ▷ (∀ cur' σ', ⌜cstep cur σ cur' σ'⌝ ={∅,E}=∗
                        gen_heap_ctx σ' ∗ wp E cur' Φ Φret))
     end)%I.

  Local Instance wp_pre_contractive : Contractive wp_pre.
  Proof.
    rewrite /wp_pre=> n wp wp' Hwp E e1 Φ.
    (* repeat (f_contractive || f_equiv); apply Hwp. *)
  Admitted.

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
  Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

  Lemma wp_skip Φ Φret E: Φ Vvoid ⊢ WP curs Sskip @ E {{ Φ; Φret }}.
  Proof.
    iIntros "HΦ".
    by rewrite wp_unfold /wp_pre.
  Qed.

  Lemma wp_value Φ Φret E v: Φ v ⊢ WP (cure (Evalue v)) @ E {{ Φ; Φret }}.
  Proof.
    iIntros "HΦ".
    by rewrite wp_unfold /wp_pre.
  Qed.
  
  (* Lemma wp_strong_mono E1 E2 c Φ Φret Ψ : *)
  (*   E1 ⊆ E2 → (∀ v, Φ v ={E2}=∗ Ψ v) ∗ WP c @ E1 {{ Φ; Φret }} ⊢ WP c @ E2 {{ Ψ; Φret }}. *)
  (* Proof. *)
  (*   iIntros (?) "[HΦ H]". iLöb as "IH" forall (c). *)
  (*   rewrite !wp_unfold /wp_pre. *)
    (* idestruct "H" as "[Hv|[% H]]"; [iLeft|iRight]. *)
    (* { iDestruct "Hv" as (v) "[% Hv]". iExists v; iSplit; first done. *)
    (*   iApply ("HΦ" with ">[-]"). by iApply (fupd_mask_mono E1 _). } *)
    (* iSplit; [done|]; iIntros (σ1) "Hσ". *)
    (* iMod (fupd_intro_mask' E2 E1) as "Hclose"; first done. *)
    (* iMod ("H" $! σ1 with "Hσ") as "[$ H]". *)
    (* iModIntro. iNext. iIntros (e2 σ2 Hstep). *)
    (* iMod ("H" $! e2 σ2 with "[#]") as "($ & H)"; auto. *)
    (* iMod "Hclose" as "_". by iApply ("IH" with "HΦ"). *)
  (* Admitted. *)

  Lemma fupd_wp E e Φ Φret: (|={E}=> WP e @ E {{ Φ; Φret }}) ⊢ WP e @ E {{ Φ; Φret }}.
  Proof.
  (*   rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?. *)
  (*   { iLeft. iExists v; iSplit; first done. *)
  (*       by iMod "H" as "[H|[% ?]]"; [iDestruct "H" as (v') "[% ?]"|]; simplify_eq. } *)
    (*   iRight; iSplit; [done|]; iIntros (σ1) "Hσ1". *)
    (* iMod "H" as "[H|[% H]]"; last by iApply "H". *)
    (* iDestruct "H" as (v') "[% ?]"; simplify_eq. *)
  Admitted.

  (* Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed. *)

  Lemma wp_bind {E e} (Kes: list exprctx) (Ks: stmtsctx) Φ Φret:
    WP cure e @ E {{ v, WP curs (fill_stmts (fill_ectxs (Evalue v) Kes) Ks) {{ Φ ; Φret }} ; Φret }}
    ⊢ WP curs (fill_stmts (fill_ectxs e Kes) Ks) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_bind_e {E e} (K: list exprctx) Φ Φret:
    WP cure e @ E {{ v, WP cure (fill_ectxs (Evalue v) K) {{ Φ ; Φret }} ; Φret }}
    ⊢ WP cure (fill_ectxs e K) @ E {{ Φ ; Φret }}.
  Admitted.
  
  Lemma wp_assign E l v v' t t' Φ Φret:
    typeof t' v' →
    ▷ l ↦ v @ t ∗ ▷ (l ↦ v' @ t' -∗ Φ Vvoid)
    ⊢ WP curs (Sassign (Evalue (Vptr l)) (Evalue v')) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_seq E s1 s2 Φ Φret:
    WP curs s1 @ E {{ _, WP curs s2 @ E {{ Φ ; Φret }} ; Φret }}
    ⊢ WP curs (Sseq s1 s2) @ E {{ Φ ; Φret }}.
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
      | _ => e
    end.
  
  Fixpoint subst_s (x: ident) (l: addr) (s: stmts) : stmts :=
    match s with
      | Sskip => Sskip
      | Sprim p => Sprim p
      | Sassign e1 e2 => Sassign (subst_e x (Evalue (Vptr l)) e1)
                                 (subst_e x (Ederef (Evalue (Vptr l))) e2)
      | Sif e s1 s2 => Sif (subst_e x (Ederef (Evalue (Vptr l))) e) (subst_s x l s1) (subst_s x l s2)
      | Swhile e s => Swhile (subst_e x (Ederef (Evalue (Vptr l))) e) (subst_s x l s)
      | Srete e => Srete (subst_e x (Ederef (Evalue (Vptr l))) e)
      | Sret => Sret
      | Scall f es => Scall f (map (subst_e x (Ederef (Evalue (Vptr l)))) es)
      | Sseq s1 s2 => Sseq (subst_s x l s1) (subst_s x l s2)
    end.

  Fixpoint substs (m: list (ident * addr)) (s: stmts) : stmts :=
    match m with
      | (i, l)::m => substs m (subst_s i l s)
      | [] => s
    end.

  Lemma wp_call (p: program) es vs params f_body f retty Φ Φret: 
    p f = Some (retty, params, f_body) →
    es = map Evalue vs →
    params_match params vs →
    (∀ ls,
       ⌜ length ls = length vs ⌝ -∗
       alloc_params (zip ls (params.*2)) vs -∗
       WP curs (substs (zip (params.*1) ls) f_body)
          {{ _, True; Φ }})
    ⊢ WP curs (Scall f es) {{ Φ; Φret }}.
  Admitted.

End rules.
