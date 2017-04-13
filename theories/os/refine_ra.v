From iris.prelude Require Export prelude.
From iris.algebra Require Import cmra dra cmra_tactics.
From iris_os.os Require Import spec.

Section algebra.
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

  Instance op_view: Op view := max_view.

  Definition cfg: Type := spec_state * spec_code.

  Record refine_car : Type :=
    Refine {
        refine_view: view;
        cfgs: list cfg;
      }.

  Definition spec_step' (c c': cfg) : Prop :=
    spec_step (c.2) (c.1) (c'.2) (c'.1).

  Inductive valid_cfgs: list cfg → Prop :=
  | VCnil: valid_cfgs []
  | VCsingle c: valid_cfgs [c]
  | VCstep c c' cs:
      spec_step' c c' →
      valid_cfgs (c :: cs) →
      valid_cfgs (c' :: c :: cs).

  Global Instance refine_equiv : Equiv refine_car := (=).

  Global Instance refine_equivalence: Equivalence ((≡) : relation refine_car).
  Proof. by split; eauto with *. Qed.

  Global Instance refine_leibniz: LeibnizEquiv refine_car.
  Proof. by intro. Qed.

  Instance refine_valid : Valid refine_car := λ r, valid_cfgs (cfgs r).

  Instance refine_core : Core refine_car := λ r, Refine snapshot (cfgs r).

  Inductive refine_disjoint : Disjoint refine_car :=
  | snap_snap_disjoint cs1 cs2 :
      (prefix cs1 cs2 ∨ prefix cs2 cs1) →
      Refine snapshot cs1 ⊥ Refine snapshot cs2
  | snap_master_disjoint cs1 cs2:
      Refine snapshot cs1 ⊥ Refine master (cs2 ++ cs1)
  | master_snapshot_disjoint cs1 cs2:
      Refine master (cs2 ++ cs1) ⊥ Refine snapshot cs1.

  Existing Instance refine_disjoint.

  Instance op_cfgs: Op (list cfg) :=
    λ cs1 cs2, if (Nat.leb (length cs1) (length cs2)) then cs2 else cs1.

  Instance assoc_op_cfgs: Assoc (@eq (list cfg)) (⋅).
  Admitted.

  Instance comm_op_cfgs: Comm (@eq (list cfg)) (⋅).
  Admitted.

  Instance op_refine : Op refine_car :=
    λ r1 r2, Refine (refine_view r1 ⋅ refine_view r2) (cfgs r1 ⋅ cfgs r2).

  Lemma refine_op v1 v2 l1 l2: Refine v1 l1 ⋅ Refine v2 l2 = Refine (v1 ⋅ v2) (l1 ⋅ l2).
  Proof. unfold op, op_refine. by simpl. Qed.

  Lemma cfgs_id_merge (cs: list cfg): cs ⋅ cs = cs.
  Proof. unfold op, op_cfgs. by rewrite Nat.leb_refl. Qed.

  Lemma refine_id_merge cs:
    Refine master cs ⋅ Refine snapshot cs = Refine master cs.
  Proof. unfold op, op_refine. simpl. by rewrite cfgs_id_merge. Qed.

  Lemma refine_id_disj cs:
    Refine master cs ⊥ Refine snapshot cs.
  Proof.
    replace cs with ([] ++ cs) at 1;
    [ constructor | apply app_nil_l ].
  Qed.

  Lemma op_cfgs_prefix (l1 l2: list cfg): prefix l1 l2 → l1 ⋅ l2 = l2.
  Admitted.

  Lemma op_cfgs_app (l1 l2: list cfg): (l1 ++ l2) ⋅ l2 = l1 ++ l2.
  Admitted.

  Lemma refine_dra : DRAMixin refine_car.
  Proof.
    split; try apply _; auto.
    - intros.
      destruct x as [[] csx]; destruct y as [[] csy]; inversion H1;
      rewrite refine_op; simplify_eq.
      + by rewrite op_cfgs_app.
      + by rewrite comm_op_cfgs op_cfgs_app.
      + destruct H4.
        * by rewrite op_cfgs_prefix.
        * by rewrite comm_op_cfgs op_cfgs_prefix.
    - intros ???.

    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Canonical Structure refineDR : draT := DRAT refine_car refine_dra.

  Instance refine_car_empty : Empty refine_car := Refine snapshot [].

  Instance refine_discrete: CMRADiscrete (validityR (refineDR)).
  Proof. apply _. Qed.

  Definition refine_cmra := (validity (refineDR)).

  Global Instance refine_empty : Empty (refine_cmra) := to_validity (refine_car_empty).

  Lemma refine_unit: UCMRAMixin (refine_cmra).
  Proof.
    split.
    - constructor.
    - admit.
    - constructor. by simpl.
  Admitted.

  Canonical Structure refine_ucmra : ucmraT :=
    (UCMRAT refine_cmra (cmra_ofe_mixin _) (cmra_mixin _) refine_unit).

End algebra.
