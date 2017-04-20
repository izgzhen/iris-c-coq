Require Import iris_c.clang.logic.
From iris.proofmode Require Import coq_tactics tactics.
Require Import iris_c.lib.gmap_solve.

Set Default Proof Using "Type".
Import uPred.

Ltac wp_done :=
  match goal with
    | |- typeof _ _ => (fast_done || constructor || apply default_val_types)
    | |- assign_type_compatible _ _ => (fast_done || constructor)
    | _ => fast_done
  end.

Ltac solve_assign_type t :=
  match t with
    | Tptr ?t' => (apply (assign_ptr_ptr t') || apply (assign_null_ptr t'))
    | _ => constructor
  end.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)

Ltac reshape_expr e tac :=
  let rec go K e :=
  match e with
  | _ => tac (reverse K) e
  | Ebinop ?op (Evalue ?v1) ?e2 => go (EKbinopl op v1 :: K) e2
  | Ebinop ?op ?e1 ?e2 => go (EKbinopr op e2 :: K) e1
  | Efst ?e => go (EKfst :: K) e
  | Esnd ?e => go (EKsnd :: K) e
  | Ederef_typed ?t ?e => go (EKderef_typed t :: K) e
  | Eassign (Evalue (Vptr ?l)) ?e =>
    go (EKassignl l :: K) e
  | Eassign ?e1 ?e2 =>
    go (EKassignr e2 :: K) e1
  | Erete ?e =>
    go (EKrete :: K) e
  | Ewhile ?c ?e ?s =>
    go (EKwhile c s :: K) e
  | ECAS_typed ?t (Evalue (Vptr ?l)) (Evalue ?v1) ?e2 =>
    go (EKCASr t l v1 :: K) e2
  | ECAS_typed ?t (Evalue (Vptr ?l)) ?e1 ?e2 =>
    go (EKCASm t l e2 :: K) e1
  | ECAS_typed ?t ?e0 ?e1 ?e2 =>
    go (EKCASl t e1 e2 :: K) e0
  | Elet_typed ?t ?x ?ex ?ebody =>
    go (EKlet t x ebody :: K) ex
  | Eif ?e ?e1 ?e2 => go (EKif e1 e2 :: K) e
  | Ealloc ?t ?e => go (EKalloc t :: K) e
  end in go (@nil exprctx) e.

Ltac wp_bind_core Kes :=
  lazymatch eval hnf in Kes with
  | [] => etrans; [|fast_by apply (wp_bind [])]; simpl
  | _ => etrans; [|fast_by apply (wp_bind Kes)]; simpl
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E ?s ?Q => reshape_expr s ltac:(fun Kes e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core Kes
    end) || fail "wp_bind: cannot find" efoc "in" s
  | _ => fail "wp_bind: not a 'wp'"
  end.

Section heap.
Context `{clangG Σ}.

Lemma tac_wp_alloc Δ Δ' E j v t Φ :
  typeof v t →
  IntoLaterNEnvs 1 Δ Δ' →
  (∀ l, ∃ Δ'',
    envs_app false (Esnoc Enil j (l ↦ v @ t)) Δ' = Some Δ'' ∧
    (Δ'' ⊢ Φ (Vptr l))) →
  Δ ⊢ WP Ealloc t (Evalue v) @ E {{ Φ }}.
Proof.
  intros ?? HΔ. eapply (wand_apply True%I).
  { iApply wp_alloc; first done. }
  rewrite left_id into_laterN_env_sound; apply later_mono, forall_intro=> l.
  destruct (HΔ l) as (Δ''&?&HΔ'). rewrite envs_app_sound //; simpl.
  by rewrite right_id HΔ'.
Qed.

Lemma tac_wp_assign Δ Δ' Δ'' E i l (v v': val) (t t': type) Φ:
  typeof v' t' → assign_type_compatible t t' →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v @ t)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v' @ t)) Δ' = Some Δ'' →
  (Δ'' ⊢ Φ Vvoid) →
  Δ ⊢ WP Eassign (Evalue (Vptr l)) (Evalue v') @ E {{ Φ }}.
Proof.
  intros. eapply wand_apply.
  { iIntros "HP HQ". iApply wp_assign; [done|done|].
    iSplitL "HP"; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. apply later_mono, sep_mono_r, wand_mono=>//.
Qed.

Lemma tac_wp_load Δ Δ' E i l q v t Φ:
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v @ t)%I →
  (Δ' ⊢ Φ v) →
  Δ ⊢ WP (Ederef_typed t (Evalue (Vptr l))) @ E {{ Φ }}.
Proof.
  intros. eapply wand_apply.
  { iIntros "HP HQ". iApply wp_load. iSplitL "HP"; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

End heap.

Tactic Notation "wp_skip" := iApply wp_skip; iNext.

Tactic Notation "wp_assign" :=
  iStartProof;
  repeat (iApply wp_seq; first by simpl);
  lazymatch goal with
  | |- _ ⊢ wp ?E (Eassign (Evalue (Vptr ?l)) (Evalue ?rv)) ?P =>
    iMatchHyp (fun H P => match P with (l ↦{_} _ @ ?t)%I =>
      (match goal with
         | [ H : typeof rv _ |- _ ] => idtac
         | _ => assert (typeof rv t) by constructor
      end);
        eapply tac_wp_assign;
        [let v := match goal with |- typeof ?v ?t => v end in
         wp_done || fail "wp_store:" v "doesn't type check"
        |solve_assign_type t || fail "wp_assign: assignment types are not compatible"
        |apply _
        |let l := match goal with |- _ = Some (_, (?l ↦{_} _ @ _)%I) => l end in
         iAssumptionCore || fail "wp_assign: cannot find" l "↦ ?"
        |env_cbv; reflexivity
        | auto (* wp_finish *)]
    end); try wp_skip
  | _ => fail "wp_assign: not a 'wp'"
  end.

Tactic Notation "wp_alloc" ident(l) "as" constr(H) :=
  iStartProof;
  repeat (iApply wp_seq; first by simpl);
  lazymatch goal with
  | |- _ ⊢ wp ?E ?e ?Q =>
    first
      [reshape_expr e ltac:(fun K e' =>
         match eval hnf in e' with Ealloc _ _ => wp_bind_core K end)
      |fail 1 "wp_alloc: cannot find 'Alloc' in" e];
    eapply tac_wp_alloc with (j:=H);
      [ wp_done || fail "wp_alloc: not typeof"
      | apply _
      | first [intros l | fail 1 "wp_alloc:" l "not fresh"];
        eexists; split;
          [ env_cbv; reflexivity || fail "wp_alloc:" H "not fresh"
          | auto ]]
  | _ => fail "wp_alloc: not a 'wp'"
end.

Tactic Notation "wp_load" :=
  iStartProof;
  repeat (iApply wp_seq; first by simpl);
  lazymatch goal with
  | |- _ ⊢ wp ?E ?s ?P =>
    first
      [reshape_expr s ltac:(fun Kes e' =>
         match eval hnf in e' with Ederef_typed _ (Evalue _) => wp_bind_core Kes end)
      |fail 1 "wp_load: cannot find 'Ederef_typed' in" s];
    eapply tac_wp_load;
      [apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _ @ _)%I) => l end in
       iAssumptionCore || fail "wp_load: cannot find" l "↦ ?"
      | auto]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_op" :=
  iStartProof;
  repeat (iApply wp_seq; first by simpl);
  lazymatch goal with
  | |- _ ⊢ wp ?E ?s ?P => reshape_expr s ltac:(fun Kes e' =>
    lazymatch eval hnf in e' with
    | Ebinop _ _ _ => wp_bind_core Kes; iApply wp_op=>//
    end) || fail "wp_op: cannot find Ebinop in" s
  | _ => fail "wp_op: not a 'wp'"
end.

Tactic Notation "wp_fst" :=
  iStartProof;
  repeat (iApply wp_seq; first by simpl);
  lazymatch goal with
  | |- _ ⊢ wp ?E ?s ?P => reshape_expr s ltac:(fun Kes e' =>
    lazymatch eval hnf in e' with
    | Esnd _ => wp_bind_core Kes; iApply wp_fst=>//
    end) || fail "wp_op: cannot find Efst in" s
  | _ => fail "wp_op: not a 'wp'"
end.

Tactic Notation "wp_snd" :=
  iStartProof;
  repeat (iApply wp_seq; first by simpl);
  lazymatch goal with
  | |- _ ⊢ wp ?E ?s ?P => reshape_expr s ltac:(fun Kes e' =>
    lazymatch eval hnf in e' with
    | Esnd _ => wp_bind_core Kes; iApply wp_snd=>//
    end) || fail "wp_op: cannot find Esnd in" s
  | _ => fail "wp_op: not a 'wp'"
end.

Tactic Notation "wp_alloc" ident(l) :=
  let H := iFresh in wp_alloc l as H.

Tactic Notation "wp_cas_fail" :=
  iApply wp_cas_fail; last iFrame;
  [ by simpl | constructor | constructor | iNext ].

Tactic Notation "wp_cas_suc" :=
  iApply wp_cas_suc;
  [ constructor | constructor | iNext; iFrame ].

Tactic Notation "wp_ret" := iApply (wp_ret []).

Tactic Notation "wp_let" := iApply wp_let=>//; iNext.

Ltac wp_run :=
  (match goal with
   | |- _ ⊢ wp ?E (Eassign _ _) ?P => wp_assign
   | |- _ ⊢ wp ?E (Eseq _ _) ?P => wp_skip
   | |- _ ⊢ wp ?E (Ewhile _ (Evalue vfalse) _) ?P => iApply wp_while_false
   | |- _ ⊢ wp ?E (Ewhile _ (Evalue vtrue) _) ?P => iApply wp_while_true
   | |- _ => wp_snd
   | |- _ => wp_fst
   | |- _ => wp_load
   | |- _ => wp_ret
   | |- _ => wp_op
   | |- _ ⊢ ▷ _ => iNext
  end; wp_run) || idtac.

Ltac unfold_f_inst :=
  rewrite /instantiate_let /resolve_rhs; repeat gmap_simplify.
