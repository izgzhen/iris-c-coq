From iris.prelude Require Export prelude.
From iris.algebra Require Import cmra dra cmra_tactics.
From iris_os.os Require Import spec.

Section algebra.
  Context `{K : nat}.

  Inductive view : Set := master | snapshot.

  Definition max_view (v1 v2: view) :=
    match v1, v2 with
      | master, _ => master
      | _, master => master
      | _, _ => snapshot
    end.

  Instance assoc_max_view: Assoc (=) max_view.
  Proof. intros [|] [|] [|]; auto. Qed.

  Instance comm_max_view: Comm (=) max_view.
  Proof. intros [|] [|]; auto. Qed.

  Definition cfg: Type := spec_state * spec_code.

  Record refine_car (K': nat) : Type :=
    Refine {
        refine_view: view;
        cfgs: list cfg;
      }.

  Arguments refine_view {_} _.
  Arguments cfgs {_} _.
  Arguments Refine {_} _ _.

  Definition spec_step' (c c': cfg) : Prop :=
    spec_step (c.2) (c.1) (c'.2) (c'.1).

  Inductive valid_cfgs: list cfg → Prop :=
  | VCnil: valid_cfgs []
  | VCsingle c: valid_cfgs [c]
  | VCstep c c' cs:
      spec_step' c c' →
      valid_cfgs (c :: cs) →
      valid_cfgs (c' :: c :: cs).

  Global Instance refine_equiv : Equiv (refine_car K) := (=).

  Global Instance refine_equivalence: Equivalence ((≡) : relation (refine_car K)).
  Proof. by split; eauto with *. Qed.

  Global Instance refine_leibniz: LeibnizEquiv (refine_car K).
  Proof. by intro. Qed.

  Instance refine_valid : Valid (refine_car K) := λ r, valid_cfgs (cfgs r).

  Instance refine_core : Core (refine_car K) :=
    λ r, Refine snapshot (cfgs r).

  Inductive refine_disjoint : Disjoint (refine_car K) :=
  | snap_snap_disjoint cs1 cs2 :
      (prefix cs1 cs2 ∨ prefix cs2 cs1) →
      Refine snapshot cs1 ⊥ Refine snapshot cs2
  | snap_master_disjoint cs1 cs2:
      Refine snapshot cs1 ⊥ Refine master (cs2 ++ cs1)
  | master_snapshot_disjoint cs1 cs2:
      Refine master (cs2 ++ cs1) ⊥ Refine snapshot cs1.

  Existing Instance refine_disjoint.

  Instance refine_op : Op (refine_car K) :=
    λ r1 r2,
    if (Nat.leb (length (cfgs r1)) (length (cfgs r2)))
      then Refine (max_view (refine_view r1) (refine_view r2)) (cfgs r2)
      else Refine (max_view (refine_view r1) (refine_view r2)) (cfgs r1).

  Lemma refine_op' cs:
    Refine master cs ⋅ Refine snapshot cs = Refine master cs.
  Proof.
    unfold op, refine_op.
    simpl. by rewrite Nat.leb_refl.
  Qed.

  Lemma refine_disj' cs:
    Refine master cs ⊥ Refine snapshot cs.
  Proof.
    replace cs with ([] ++ cs) at 1;
    [ constructor | apply app_nil_l ].
  Qed.

  Lemma refine_dra : DRAMixin (refine_car K).
  Proof.
    split; try apply _.
  Admitted.

  Canonical Structure refineDR : draT := DRAT (refine_car K) refine_dra.

  Instance refine_car_empty : Empty (refine_car K) := Refine snapshot [].

  Instance refine_discrete: CMRADiscrete (validityR (refineDR)).
  Proof. apply _. Qed.

  Definition refine_cmra := (validity (refineDR)).

  Global Instance refine_empty : Empty (refine_cmra) := to_validity (refine_car_empty).

  Lemma refine_unit: UCMRAMixin (refine_cmra).
  Admitted.

  Canonical Structure refine_ucmra : ucmraT :=
    (UCMRAT refine_cmra (cmra_ofe_mixin _) (cmra_mixin _) refine_unit).

End algebra.
