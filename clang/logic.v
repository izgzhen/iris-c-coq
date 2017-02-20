(* Program Logic *)

Require Import lang.
From iris.base_logic Require Import gen_heap big_op.
From iris.algebra Require Import gmap agree auth.
From iris.base_logic.lib Require Import wsat fancy_updates.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Definition spec_state := gmap ident val. (* XXX: should be parameterized *)

Definition spec_rel := spec_state → option val → spec_state → Prop.

Inductive spec_code :=
| SCrel (r: spec_rel)
| SCdone (v: option val).

Inductive spec_step : spec_code → spec_state → spec_code → spec_state → Prop :=
| spec_step_rel:
    ∀ (r: spec_rel) s retv s',
      r s retv s' → spec_step (SCrel r) s (SCdone retv) s'.

(* Naive equivalence *)
Instance spec_code_equiv: Equiv spec_code := (=).

Class clangG Σ := ClangG {
  clangG_invG :> invG.invG Σ;
  clangG_memG :> gen_heapG block (list byteval) Σ;
  clangG_spstG :> gen_heapG ident val Σ;
  clangG_specG :> inG Σ (authR (optionUR (agreeR (discreteC (spec_code)))));
  spec_gname : gname
}.

Section wp.
  Context `{clangG Σ}.

  Definition γ_sstate := @gen_heap_name _ _ _ _ _ clangG_spstG.

  Definition spec_interp c0 s0 :=
    (∃ c s,
     own spec_gname (● (Some (to_agree (c : leibnizC spec_code)))) ∗
     own γ_sstate (● to_gen_heap s) ∗ ⌜ spec_step c0 s0 c s ⌝)%I.

  Definition wp_pre
           (wp: coPset -c> code -c> (val -c> iProp Σ) -c> (option val -c> iProp Σ) -c> iProp Σ) :
    coPset -c> code -c> (val -c> iProp Σ) -c> (option val -c> iProp Σ) -c> iProp Σ :=
    (λ E c Φ Φret,
     (* value case *)
     (∃ v, ⌜to_val c = Some v⌝ ∧ |={E}=> Φ v) ∨
     (* return case *) (* XXX: return nothing case *)
     (∃ v k, ⌜ c = (curs (Srete (Evalue v)), k) ⌝ ∧ |={E}=> Φret (Some v) ) ∨
     (* step case *)
     (⌜to_val c = None⌝ ∧
      ((∀ (σ: mem),
          gen_heap_ctx σ ={E,∅}=∗
            ⌜reducible c⌝ ∗
            ▷ (∀ c' σ', ⌜head_step c σ c' σ'⌝ ={∅,E}=∗
            gen_heap_ctx σ' ∗ wp E c' Φ Φret)) ∨
       (∀ c0 s0,
          spec_interp c0 s0 ={E, ∅}=∗
          ▷ |={∅,E}=> spec_interp c0 s0 ∗ wp E c Φ Φret))))%I.

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
    coPset → code → (val → iProp Σ) → (option val → iProp Σ) → iProp Σ := fixpoint wp_pre.
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

Notation "l ↦{ q } v @ t" := (mapstoval l q v t)
  (at level 20, q at level 50, format "l  ↦{ q }  v  @  t") : uPred_scope.
Notation "l ↦ v @ t" :=
  (mapstoval l 1%Qp v t) (at level 20) : uPred_scope.
Notation "l ↦{ q } -" := (∃ v t, l ↦{q} v @ t)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : uPred_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : uPred_scope.

Notation "l S↦ v" :=
  (@mapsto _ _ _ _ _ clangG_spstG l 1%Qp v) (at level 20) : uPred_scope.

Section rules.
  Context `{clangG Σ}.

  Definition sstate (s: spec_state) := ([⋅ map] l ↦ v ∈ s, l S↦ v)%I.
  Definition scode (c: spec_code) := own spec_gname (◯ (Some (to_agree (c: leibnizC spec_code)))).
  
  Lemma wp_unfold E c Φ Φret: WP c @ E {{ Φ; Φret }} ⊣⊢ wp_pre wp E c Φ Φret.
  Proof. rewrite wp_eq. apply (fixpoint_unfold wp_pre). Qed.

  Lemma wp_value Φ Φret v E: Φ v ⊢ WP (of_val v) @ E {{ Φ; Φret }}.
  Proof.
    iIntros "HΦ".
    rewrite wp_unfold /wp_pre.
    iLeft. iExists v. auto.
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

  (* Lemma fupd_wp E e Φ : (|={E}=> WP e @ E {{ Φ }}) ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. *)
  (*   rewrite wp_unfold /wp_pre. iIntros "H". destruct (to_val e) as [v|] eqn:?. *)
  (*   { iLeft. iExists v; iSplit; first done. *)
  (*       by iMod "H" as "[H|[% ?]]"; [iDestruct "H" as (v') "[% ?]"|]; simplify_eq. } *)
    (*   iRight; iSplit; [done|]; iIntros (σ1) "Hσ1". *)
    (* iMod "H" as "[H|[% H]]"; last by iApply "H". *)
    (* iDestruct "H" as (v') "[% ?]"; simplify_eq. *)
  (* Admitted. *)

  (* Lemma wp_fupd E e Φ : WP e @ E {{ v, |={E}=> Φ v }} ⊢ WP e @ E {{ Φ }}. *)
  (* Proof. iIntros "H". iApply (wp_strong_mono E); try iFrame; auto. Qed. *)

  Lemma fill_step_inv K e1' σ1 e2 σ2 :
    to_val (e1', knil) = None → head_step (e1', K) σ1 e2 σ2 →
    ∃ e2', e2 = (e2', K) ∧ head_step (e1', knil) σ1 (e2', knil) σ2.
  Admitted.

  Lemma wp_cont E k s Φ Φret:
    WP (curs s, knil) @ E {{ v, WP (curs Sskip, k) @ E {{ Φ; Φret }} ; Φret }}
       ⊢ WP (curs s, k) @ E {{ Φ; Φret }}.
  Admitted.

  Lemma wp_conte E k e Φ Φret:
    WP (cure e, knil) @ E {{ v, WP (cure (Evalue v), k) @ E {{ Φ ; Φret }} ; Φret }}
       ⊢ WP (cure e, k) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_bind e Ke ke ks E Φ Φret:
    WP (cure e, (Ke::ke, ks)) @ E {{ Φ ; Φret }}
    ⊢ WP (cure (fill_expr Ke e), (ke, ks)) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_unbind e Ke ke ks E Φ Φret:
    WP (cure (fill_expr Ke e), (ke, ks)) @ E {{ Φ ; Φret }}
    ⊢ WP (cure e, (Ke::ke, ks)) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_bind_s e Ks ks E Φ Φret:
    WP (cure e, ([], Ks::ks)) @ E {{ Φ; Φret }}
       ⊢ WP (curs (fill_stmts Ks e), ([], ks)) @ E {{ Φ; Φret }}.
  Admitted.

  Lemma wp_unbind_s e Ks ks E Φ Φret:
    WP (curs (fill_stmts Ks e), ([], ks)) @ E {{ Φ ; Φret }}
    ⊢ WP (cure e, ([], Ks::ks)) @ E {{ Φ ; Φret }}.
  Admitted.
 
  (* High-level Assertions *)
  
  Lemma wp_assign E l t v Φ Φret:
    typeof t v →
    l ↦ - ∗ (l ↦ v @ t -∗ Φ)
    ⊢ WP (curs (Sassign (Evalue (Vptr l)) (Evalue v)), knil) @ E {{ _, Φ ; Φret }}.
  Admitted.

  Lemma wp_seq E s1 s2 Φ Φret:
    WP (curs s1, knil) @ E {{ _, WP (curs s2, knil) @ E {{ Φ ; Φret }} ; Φret }}
    ⊢ WP (curs (Sseq s1 s2), knil) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_load E Φ p v t q Φret:
    p ↦{q} v @ t ∗ (p ↦{q} v @ t -∗ Φ v)
    ⊢ WP (cure (Ederef (Evalue (Vptr p))), knil) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_op E op v1 v2 v' Φ Φret:
    evalbop op v1 v2 = Some v' →
    Φ v' ⊢ WP (cure (Ebinop op (Evalue v1) (Evalue v2)), knil) @ E {{ Φ ; Φret }}.
  Admitted.

  Lemma wp_ret E v Φ Φret k:
    Φret (Some v)
    ⊢ WP (curs (Srete (Evalue v)), k) @ E {{ Φ; Φret }}.
  Admitted.

  Lemma wp_spec E ss sc ss' sc' c Φ Φret:
  sstate ss ∗ scode sc ∗
  ⌜ spec_step sc ss sc' ss' ⌝ ∗ ⌜ to_val c = None ⌝ ∗ (* to_val condition might be redundant *)
  (sstate ss' -∗ scode sc' -∗ WP c @ E {{ Φ; Φret }})
  ⊢ WP c @ E {{ Φ; Φret }}.
  Admitted.

End rules.

Section example.
  Context `{clangG Σ}.
  
  Parameter px py: addr.
  Parameter Y: ident.

  Definition x := Evalue (Vptr px).
  Definition y := Evalue (Vptr py).
  
  Definition f_body : stmts :=
    Sassign x (Ebinop oplus (Ederef y) (Ederef x)) ;;;
    Sassign y (Ederef x) ;;;
    Srete (Ederef x).

  Definition f_rel (vx: int) (s: spec_state) (r: option val) (s': spec_state) :=
    ∃ vy:int, s !! Y = Some (Vint32 vy) ∧
              r = Some (Vint32 (Int.add vx vy)) ∧
              s' = <[ Y := (Vint32 (Int.add vx vy)) ]> s.

  Definition I := (∃ vy, py ↦ Vint32 vy @ Tint32 ∗ Y S↦ Vint32 vy)%I.

  Lemma mapsto_singleton l v:
    l S↦ v ⊣⊢ sstate {[ l := v ]}.
  Proof. by rewrite /sstate big_sepM_singleton. Qed.
  
  Lemma f_spec vx Φ Φret:
    px ↦ Vint32 vx @ Tint32 ∗ I ∗ scode (SCrel (f_rel vx)) ∗
    (∀ v, px ↦ v @ Tint32 -∗ I -∗
          scode (SCdone (Some v)) -∗ Φret (Some v))
    ⊢ WP (curs f_body, knil) {{ Φ ; Φret }}.
  Proof.
    iIntros "(Hx & HI & Hsc & HΦret)".
    iDestruct "HI" as (vy) "[Hy HY]".
    iApply (wp_spec _ {[ Y := (Vint32 vy) ]} _
                    {[ Y := (Vint32 (Int.add vy vx)) ]} (SCdone (Some (Vint32 (Int.add vy vx))))).
    iFrame. iSplitL "HY"; first by iApply mapsto_singleton.
    iSplitL "".
    { iPureIntro.
      apply spec_step_rel. unfold f_rel.
      exists vy. admit. }
    simpl. iSplit; first done.
    iIntros "Hss HSc".
    iApply wp_seq.
    rewrite /example.x /example.y.
    iApply (wp_bind_s _ (SKassignl _)).
    iApply (wp_bind _ (EKbinopr _ _)).
    iApply wp_conte.
    iApply wp_load. iFrame "Hy". iIntros "Hy". (* XXX: use wp_load tactic *)
    iApply (wp_unbind _ (EKbinopr _ _)).
    simpl. iApply (wp_bind _ (EKbinopl _ _)).
    iApply wp_conte.
    iApply wp_load. iFrame "Hx". iIntros "Hx".
    iApply (wp_unbind _ (EKbinopl _ _)).
    simpl.
    iApply wp_conte.
    iApply wp_op=>//.
    iApply (wp_unbind_s _ (SKassignl _)).
    simpl.
    iApply wp_assign; first by apply typeof_int32.
    iSplitL "Hx"; first eauto.
    iIntros "Hx".
    iApply wp_seq.
    iApply (wp_bind_s _ (SKassignl _)).
    iApply wp_conte.
    iApply wp_load. iFrame "Hx". iIntros "Hx".
    iApply (wp_unbind_s _ (SKassignl _)).
    simpl. iApply wp_assign; first by apply typeof_int32.
    iSplitL "Hy"; first eauto. iIntros "Hy".
    iApply (wp_bind_s _ SKrete).
    iApply wp_conte. iApply wp_load.
    iFrame "Hx". iIntros "Hx".
    iApply (wp_unbind_s _ SKrete). simpl.
    iApply wp_ret.
    iSpecialize ("HΦret" $! (Vint32 (Int.add vy vx)) with "Hx").
    iApply ("HΦret" with "[Hss Hy]")=>//.
    iExists (Int.add vy vx). iFrame. by iApply mapsto_singleton.
  Admitted.
    
End example.

