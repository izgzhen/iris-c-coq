From iris_c.clang Require Import tactics ret_logic.
From iris.proofmode Require Import coq_tactics tactics.

Ltac wpr_bind_core Kes :=
  lazymatch eval hnf in Kes with
  | [] => etrans; [|fast_by apply (wpr_bind [])]; simpl
  | _ => etrans; [|fast_by apply (wpr_bind Kes)]; simpl
  end.

Tactic Notation "wpr_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- _ ⊢ wpr ?E ?s ?Q ?Q2 => reshape_expr s ltac:(fun Kes e' =>
    match e' with
    | efoc => unify e' efoc; wpr_bind_core Kes
    end) || fail "wpr_bind: cannot find" efoc "in" s
  | _ => fail "wpr_bind: not a 'wpr'"
  end.
