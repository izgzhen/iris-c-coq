Require Import iris_os.clang.logic.
From iris.proofmode Require Import coq_tactics tactics.
Require Import iris_os.lib.gmap_solve.

Set Default Proof Using "Type".
Import uPred.

Ltac wp_done :=
  match goal with
    | |- typeof _ _ => (fast_done || constructor)
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
  | _ => tac K e
  | Ebinop ?op (Evalue ?v1) ?e2 => go (EKbinopl op v1 :: K) e2
  | Ebinop ?op ?e1 ?e2 => go (EKbinopr op e2 :: K) e1
  | Efst ?e => go (EKfst :: K) e
  | Esnd ?e => go (EKsnd :: K) e
  | Ederef_typed ?t ?e => go (EKderef_typed t :: K) e
  end in go (@nil exprctx) e.

Ltac reshape_stmts s tac :=
  match s with
    | Sassign (Evalue (Vptr ?l)) ?e =>
      reshape_expr e ltac:(fun Kes e' => tac Kes (SKassignl l) e')
    | Sassign ?e1 ?e2 =>
      reshape_expr e1 ltac:(fun Kes e' => tac Kes (SKassignr e2) e')
    | Srete ?e =>
      reshape_expr e ltac:(fun Kes e' => tac Kes SKrete e')
    | Swhile ?c ?e ?s =>
      reshape_expr e ltac:(fun Kes e' => tac Kes (SKwhile c s) e')
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

Section heap.
Context `{clangG Σ}.

Lemma tac_wp_assign Δ Δ' Δ'' E i l (v v': val) (t t': type) Φ Φret:
  typeof v' t' → assign_type_compatible t t' →
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦ v @ t)%I →
  envs_simple_replace i false (Esnoc Enil i (l ↦ v' @ t)) Δ' = Some Δ'' →
  (Δ'' ⊢ Φ Vvoid) →
  Δ ⊢ WP curs (Sassign (Evalue (Vptr l)) (Evalue v')) @ E {{ Φ ; Φret }}.
Proof.
  intros. eapply wand_apply.
  { iIntros "HP HQ". iApply wp_assign; [done|done|].
    iSplitL "HP"; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl.
  rewrite right_id. apply later_mono, sep_mono_r, wand_mono=>//.
Qed.

(* Lemma tac_wp_assign_offset Δ Δ' Δ'' E i b (o: nat) (v1 v2 v2': val) (t1 t2 t2': type) Φ Φret: *)
(*   typeof v2' t2' → assign_type_compatible t2 t2' → *)
(*   IntoLaterNEnvs 1 Δ Δ' → *)
(*   envs_lookup i Δ' = Some (false, (b, o) ↦ Vpair v1 v2 @ Tprod t1 t2)%I → *)
(*   envs_simple_replace i false (Esnoc Enil i ((b, o) ↦ Vpair v1 v2' @ Tprod t1 t2)) Δ' = Some Δ'' → *)
(*   (Δ'' ⊢ Φ Vvoid) → *)
(*   Δ ⊢ WP curs (Sassign (Evalue (Vptr (b, (o + sizeof t1)%nat))) (Evalue v2')) @ E {{ Φ ; Φret }}. *)
(* Proof. *)
(*   intros. eapply wand_apply. *)
(*   { iIntros "HP HQ". iApply wp_assign_offset; [done|done|]. *)
(*     iSplitL "HP"; eauto. } *)
(*   rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl. *)
(*   rewrite right_id. apply later_mono, sep_mono_r, wand_mono=>//. *)
(* Qed. *)

Lemma tac_wp_load Δ Δ' E i l q v t Φ Φret:
  IntoLaterNEnvs 1 Δ Δ' →
  envs_lookup i Δ' = Some (false, l ↦{q} v @ t)%I →
  (Δ' ⊢ Φ v) →
  Δ ⊢ WP (cure (Ederef_typed t (Evalue (Vptr l)))) @ E {{ Φ ; Φret }}.
Proof.
  intros. eapply wand_apply.
  { iIntros "HP HQ". iApply wp_load. iSplitL "HP"; eauto. }
  rewrite into_laterN_env_sound -later_sep envs_lookup_split //; simpl.
  by apply later_mono, sep_mono_r, wand_mono.
Qed.

End heap.

Tactic Notation "wp_assign" :=
  iStartProof;
  repeat (iApply wp_seq);
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs (Sassign (Evalue (Vptr ?l)) (Evalue ?rv))) ?P ?Q =>
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
    end)
  | _ => fail "wp_assign: not a 'wp'"
  end.

Tactic Notation "wp_load" :=
  iStartProof;
  repeat (iApply wp_seq);
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs ?s) ?P ?Q =>
    first
      [reshape_stmts s ltac:(fun Kes Ks e' =>
         match eval hnf in e' with Ederef_typed _ (Evalue _) => wp_bind_core Kes Ks end)
      |fail 1 "wp_load: cannot find 'Ederef_typed' in" s];
    eapply tac_wp_load;
      [apply _
      |let l := match goal with |- _ = Some (_, (?l ↦{_} _ @ _)%I) => l end in
       iAssumptionCore || fail "wp_load: cannot find" l "↦ ?"
      |(* wp_finish *) auto]
  | _ => fail "wp_load: not a 'wp'"
  end.

Tactic Notation "wp_op" :=
  iStartProof;
  repeat (iApply wp_seq);
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

Ltac unfold_f_inst :=
  rewrite /instantiate_f_body /resolve_rhs; repeat gmap_rewrite.
