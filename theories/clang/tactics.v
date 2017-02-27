Require Import clang.logic.
From iris.proofmode Require Import coq_tactics tactics.
Set Default Proof Using "Type".
Import uPred.

Ltac solve_typeof :=
  match goal with
    | |- typeof _ (Vint32 _) => apply typeof_int32
    | |- typeof _ (Vint8 _) => apply typeof_int8
    | |- typeof Tnull Vnull => apply typeof_null
    | |- typeof _ Vnull => apply typeof_null_ptr
    | |- typeof (Tptr _) (Vptr _) => apply typeof_ptr
  end.

Lemma typeof_any_ptr (t1 t2: type) (v: val):
  typeof (Tptr t1) v → typeof (Tptr t2) v.
Proof.
  induction v; intros H; try (inversion H); try solve_typeof.
Qed.

Ltac wp_done :=
  match goal with
  | |- typeof _ _ => solve_typeof
  | _ => fast_done
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
  (* | If ?e0 ?e1 ?e2 => go (IfCtx e1 e2 :: K) e0 *)
  (* | Pair ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (PairRCtx v1 :: K) e2) *)
  (* | Pair ?e1 ?e2 => go (PairLCtx e2 :: K) e1 *)
  | Efst ?e => go (EKfst :: K) e
  | Esnd ?e => go (EKsnd :: K) e
  (* | InjL ?e => go (InjLCtx :: K) e *)
  (* | InjR ?e => go (InjRCtx :: K) e *)
  (* | Case ?e0 ?e1 ?e2 => go (CaseCtx e1 e2 :: K) e0 *)
  (* | Alloc ?e => go (AllocCtx :: K) e *)
  | Ederef ?e => go (EKderef :: K) e
  (* | Store ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (StoreRCtx v1 :: K) e2) *)
  (* | Store ?e1 ?e2 => go (StoreLCtx e2 :: K) e1 *)
  (* | CAS ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first *)
  (*    [ reshape_val e1 ltac:(fun v1 => go (CasRCtx v0 v1 :: K) e2) *)
  (*    | go (CasMCtx v0 e2 :: K) e1 ]) *)
  (* | CAS ?e0 ?e1 ?e2 => go (CasLCtx e1 e2 :: K) e0 *)
  end in go (@nil exprctx) e.

Ltac reshape_stmts s tac :=
  match s with
    | Sassign (Evalue (Vptr ?l)) ?e =>
      reshape_expr e ltac:(fun Kes e' => tac Kes (SKassignl l) e')
    | Srete ?e =>
      reshape_expr e ltac:(fun Kes e' => tac Kes SKrete e')
    | Swhile ?c ?e ?s =>
      reshape_expr e ltac:(fun Kes e' => tac Kes (SKwhile c s) e')
  end.

Ltac wp_bind_e_core K :=
  lazymatch eval hnf in K with
  | [] => idtac
  | _ => etrans; [|fast_by apply (wp_bind_e K)]; simpl
  end.

Tactic Notation "wp_bind_e" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wp ?E (cure ?e) ?Q ?P => reshape_expr e ltac:(fun K e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_e_core K
    end) || fail "wp_bind_e: cannot find" efoc "in" e
  | _ => fail "wp_bind_e: not a 'wp'"
  end.

Ltac wp_bind_core Kes Ks :=
  lazymatch eval hnf in Kes with
  | [] => etrans; [|fast_by apply (wp_bind [] Ks)]; simpl
  | _ => etrans; [|fast_by apply (wp_bind Kes Ks)]; simpl
  end.

Tactic Notation "wp_bind" open_constr(efoc) :=
  iStartProof;
  try (iApply wp_seq);
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs ?s) ?Q ?P => reshape_stmts s ltac:(fun Kes Ks e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core Kes Ks
    end) || fail "wp_bind: cannot find" efoc "in" s
  | _ => fail "wp_bind: not a 'wp'"
  end.

Section heap.
Context `{clangG Σ}.

Lemma tac_wp_assign Δ Δ' Δ'' E i l (v v': val) (t: type) Φ Φret:
  typeof t v' →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v @ t)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v' @ t)) Δ' = Some Δ'' →
  (Δ'' ⊢ Φ Vvoid) →
  Δ ⊢ WP curs (Sassign (Evalue (Vptr l)) (Evalue v')) @ E {{ Φ ; Φret }}.
Proof.
  intros. eapply wand_apply.
  { iIntros "HP HQ". iApply wp_assign; first done.
    iSplitL "HP"; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. apply later_mono, sep_mono_r, wand_mono=>//.
Qed.

Lemma tac_wp_load Δ Δ' E i l q v t Φ Φret:
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v @ t)%I →
  (Δ' ⊢ Φ v) →
  Δ ⊢ WP (cure (Ederef (Evalue (Vptr l)))) @ E {{ Φ ; Φret }}.
Proof.
  intros. eapply wand_apply.
  { iIntros "HP HQ". iApply wp_load. iSplitL "HP"; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

End heap.

Tactic Notation "wp_assign" :=
  iStartProof;
  try (iApply wp_seq);
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs (Sassign ?e _)) ?P ?Q =>
    eapply tac_wp_assign;
      [let v := match goal with |- typeof ?t ?v => v end in
       wp_done || fail "wp_store:" v "doesn't type check"
      |apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _ @ _)%I) => l end in
       iAssumptionCore || fail "wp_assign: cannot find" l "↦ ? @ ?"
      |env_cbv; reflexivity
      | auto (* wp_finish *)]
  | _ => fail "wp_assign: not a 'wp'"
  end.

Tactic Notation "wp_load" :=
  iStartProof;
  try (iApply wp_seq);
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs ?s) ?P ?Q =>
    first
      [reshape_stmts s ltac:(fun Kes Ks e' =>
         match eval hnf in e' with Ederef _ => wp_bind_core Kes Ks end)
      |fail 1 "wp_load: cannot find 'Ederef' in" s];
    eapply tac_wp_load;
      [apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _ @ _)%I) => l end in
       iAssumptionCore || fail "wp_load: cannot find" l "↦ ? @ ?"
      |(* wp_finish *) auto]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_op" :=
  iStartProof;
  try (iApply wp_seq);
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs ?s) ?P ?Q => reshape_stmts s ltac:(fun Kes Ks e' =>
    lazymatch eval hnf in e' with
    | Ebinop _ _ _ => wp_bind_core Kes Ks; iApply wp_op=>//
    end) || fail "wp_op: cannot find Ebinop in" s
  | _ => fail "wp_op: not a 'wp'"
end.

Ltac wp_run :=
  (match goal with
   | |- _ ⊢ wp ?E (curs (Sassign _ _)) ?P ?Q => wp_assign
   | |- _ ⊢ wp ?E (curs (Sseq _ _)) ?P ?Q => iApply wp_seq
   | |- _ => wp_load
   | |- _ => wp_op
  end; wp_run) || idtac.
