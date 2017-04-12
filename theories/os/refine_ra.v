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

  Instance refine_op : Op refine_car :=
    λ r1 r2,
    if (Nat.leb (length (cfgs r1)) (length (cfgs r2)))
      then Refine (refine_view r1 ⋅ refine_view r2) (cfgs r2)
      else Refine (refine_view r1 ⋅ refine_view r2) (cfgs r1).

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

  Lemma prefix_leq {A: Type} (l1 l2: list A): prefix l1 l2 → length l1 <=? length l2 = true.
  Admitted.

  Lemma prefix_geq {A: Type} (l1 l2: list A): prefix l1 l2 → length l2 <=? length l1 = false.
  Admitted.
  
  Lemma refine_dra : DRAMixin refine_car.
  Proof.
    split; try apply _; auto.
    - intros. destruct x as [[] csx]; destruct y as [[] csy].
      + inversion H1.
      + inversion H1. unfold op, refine_op. simpl.
        assert (length (cs2 ++ csy) <=? length csy = false); first admit.
        rewrite H2. simplify_eq. eauto.
      + inversion H1. unfold op, refine_op. simpl.
        assert ((length csx) <=? length (cs2 ++ csx) = true); first admit.
        rewrite H2. simplify_eq. eauto.
      + inversion H1. destruct H4.
        * simplify_eq. unfold op, refine_op. simpl.
          rewrite prefix_leq=>//.
        * simplify_eq. unfold op, refine_op. simpl.
          rewrite prefix_geq=>//. (* not very right ... but let's take it for now *)
    - admit.
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
