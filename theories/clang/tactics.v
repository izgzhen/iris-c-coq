Require Import clang.logic.
From iris.proofmode Require Import coq_tactics tactics.
Set Default Proof Using "Type".
Import uPred.

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
  (* | Fst ?e => go (FstCtx :: K) e *)
  (* | Snd ?e => go (SndCtx :: K) e *)
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
  end.

(* Ltac reshape_cur cur tac := *)
(*   match cur with *)
(*     | cure ?e => reshape_expr e ltac:(fun K e' => tac K (cure e')) *)
(*     | curs ?s => reshape_stmts s tac *)
  (* end. *)

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
  lazymatch goal with
  | |- _ ⊢ wp ?E (curs ?s) ?Q ?P => reshape_stmts s ltac:(fun Kes Ks e' =>
    match e' with
    | efoc => unify e' efoc; wp_bind_core Kes Ks
    end) || fail "wp_bind: cannot find" efoc "in" s
  | _ => fail "wp_bind: not a 'wp'"
  end.


(* Section heap. *)
(* Context `{clangG Σ}. *)

(* Lemma tac_wp_assign Δ Δ' Δ'' E i l (v v': val) (t t': type) Φ Φret: *)
(*   typeof t' v' → *)
(*   IntoLaterNEnvs 1 Δ Δ' → *)
(*   envs_lookup i Δ' = Some (false, l ↦ v @ t)%I → *)
(*   envs_simple_replace i false (Esnoc Enil i (l ↦ v' @ t')) Δ' = Some Δ'' → *)
(*   (Δ'' ⊢ Φ Vvoid) → *)
(*   Δ ⊢ WP curs (Sassign (Evalue (Vptr l)) (Evalue v')) @ E {{ Φ ; Φret }}. *)
(* Proof. *)
(*   intros. eapply wand_apply. *)
(*   { iIntros "HP HQ". iApply wp_assign; first done. *)
(*     iSplitL "HP"; eauto. } *)
(*   rewrite into_laterN_env_sound -later_sep envs_simple_replace_sound //; simpl. *)
(*   rewrite right_id. apply later_mono, sep_mono_r, wand_mono=>//. *)
(* Qed. *)


(* Tactic Notation "wp_assign" := *)
(*   iStartProof; *)
(*   lazymatch goal with *)
(*   | |- _ ⊢ wp ?E ?cur ?Q ?P => *)
(*     first *)
(*       [reshape_expr cur ltac:(fun K cur' => *)
(*          match eval hnf in cur' with (curs (Sassign _ _)) => wp_bind_core K end) *)
(*       |fail 1 "wp_assign: cannot find 'Sassign' in" cur]; *)
(*     eapply tac_wp_assign; *)
(*       [let cur' := match goal with |- to_val ?cur' = _ => cur' end in *)
(*        auto (* wp_done *) || fail "wp_assign:" cur' "not a value" *)
(*       |apply _ *)
(*       |let l := match goal with |- _ = Some (_, (?l ↦{_} _ @ _)%I) => l end in *)
(*        iAssumptionCore || fail "wp_assign: cannot find" l "↦ ? @ ?" *)
(*       |env_cbv; reflexivity *)
(*       | auto (* wp_finish *)] *)
(*   | _ => fail "wp_assign: not a 'wp'" *)
(*   end. *)


(* End heap. *)


