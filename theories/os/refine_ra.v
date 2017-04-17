From iris.prelude Require Export prelude.
From iris.algebra Require Import cmra dra cmra_tactics.
From iris_os.os Require Import spec.
From iris_os.lib Require Import prelude.

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
      (suffix cs1 cs2 ∨ suffix cs2 cs1) →
      Refine snapshot cs1 ⊥ Refine snapshot cs2
  | snap_master_disjoint cs1 cs2:
      Refine snapshot cs1 ⊥ Refine master (cs2 ++ cs1)
  | master_snapshot_disjoint cs1 cs2:
      Refine master (cs2 ++ cs1) ⊥ Refine snapshot cs1.

  Existing Instance refine_disjoint.

  Instance op_cfgs: Op (list cfg) :=
    λ cs1 cs2, if (Nat.leb (length cs1) (length cs2)) then cs2 else cs1.

  Instance assoc_op_cfgs: Assoc (@eq (list cfg)) (⋅).
  Proof.
    intros ???; unfold op, op_cfgs.
    destruct (length x <=? length y) eqn:Hxy;
      destruct (length y <=? length z) eqn:Hyz=>//.
    - by erewrite leb_trans.
    - by rewrite Hxy.
    - rewrite Hxy. erewrite gtb_trans=>//.
  Qed.

  Instance op_refine : Op refine_car :=
    λ r1 r2, Refine (refine_view r1 ⋅ refine_view r2) (cfgs r1 ⋅ cfgs r2).

  Lemma refine_op v1 v2 l1 l2:
    Refine v1 l1 ⋅ Refine v2 l2 = Refine (max_view v1 v2) (l1 ⋅ l2).
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

  Lemma op_cfgs_suffix (l1 l2: list cfg): suffix l1 l2 → l1 ⋅ l2 = l2.
  Proof.
    intros H. apply suffix_length in H.
    unfold op, op_cfgs.
    apply Nat.leb_le in H. by rewrite H.
  Qed.

  Lemma op_cfgs_app (l1 l2: list cfg): (l1 ++ l2) ⋅ l2 = l1 ++ l2.
  Proof.
    unfold op, op_cfgs.
    rewrite app_length.
    destruct l1.
    - simpl. by rewrite Nat.leb_refl.
    - by rewrite leb_cancel_false.
  Qed.

  Lemma op_cfgs_suffix' (l1 l2: list cfg): suffix l1 l2 → l2 ⋅ l1 = l2.
  Proof. intros H. inversion H. subst. apply op_cfgs_app. Qed.

  Lemma comm_op_cfgs l1 l2: l1 ⋅ (l2 ++ l1) = (l2 ++ l1) ⋅ l1.
  Proof.
    rewrite op_cfgs_app.
    destruct l2.
    - simpl. apply cfgs_id_merge.
    - simpl. unfold op, op_cfgs. by rewrite leb_cancel_true.
  Qed.

  Lemma suffix_app (lx ly: list cfg):
    ∀ l1 l2,
      l1 ++ lx = l2 ++ ly →
      lx `suffix_of` ly ∨ ly `suffix_of` lx.
  Proof.
    induction l1; induction l2; intros; simpl in H; subst.
    - by left.
    - right. rewrite app_comm_cons. by eexists.
    - left. rewrite app_comm_cons. by eexists.
    - eapply IHl1. by inversion H.
  Qed.

  Lemma suffix_trans (l1 l2 l3: list cfg):
    suffix l1 l2 → suffix l2 l3 → suffix l1 l3.
  Proof.
    intros [? ?] [? ?].
    simplify_eq. rewrite assoc. by eexists _.
  Qed.

  Ltac rewrite_op_cfgs :=
    repeat (match goal with
            | [ |- context [(?E1 ++ ?E2) ⋅ ?E2 ] ] =>
              rewrite op_cfgs_app
            | [ |- context [?E2 ⋅ (?E1 ++ ?E2) ] ] =>
              rewrite comm_op_cfgs op_cfgs_app
            | [ H: context [(?E1 ++ ?E2) ⋅ ?E2 ] |- _ ] =>
              rewrite op_cfgs_app in H
            | [ H: context [?E2 ⋅ (?E1 ++ ?E2) ] |- _ ] =>
              rewrite comm_op_cfgs op_cfgs_app in H
            | [ H: ?E1 `suffix_of` ?E2 |- context [?E1 ⋅ ?E2] ] =>
              rewrite op_cfgs_suffix
            | [ H: ?E1 `suffix_of` ?E2 |- context [?E2 ⋅ ?E1] ] =>
              rewrite op_cfgs_suffix'
            | [ H: ?E1 `suffix_of` ?E2, H2: context [?E1 ⋅ ?E2] |- _ ] =>
              rewrite op_cfgs_suffix in H2
            | [ H: ?E1 `suffix_of` ?E2, H2: context [?E2 ⋅ ?E1] |- _ ] =>
              rewrite op_cfgs_suffix' in H2
            | [ H : _ `suffix_of` _ ∨ _ `suffix_of` _ |- _ ] => destruct H
            end).

  Lemma suffix_common (lx ly lz: list cfg):
    lx `suffix_of` ly →
    lz `suffix_of` ly →
    lx `suffix_of` lz ∨ lz `suffix_of` lx.
  Proof.
    inversion 1. inversion 1.
    simplify_eq. by eapply suffix_app.
  Qed.

  Lemma refine_dra : DRAMixin refine_car.
  Proof.
    split; try apply _; auto.
    - intros x y ? ? Hdisj.
      destruct x as [[] csx]; destruct y as [[] csy]; inversion Hdisj;
      rewrite refine_op; simplify_eq; by rewrite_op_cfgs.
    - intros x y z. destruct x, y, z.
      by rewrite !refine_op !assoc.
    - intros [[] lx] [[] ly] [[] lz];
      rewrite !refine_op; simpl; intros=>//;
      match goal with
        | [H : Refine master _ ⊥ Refine master _ |- _ ] => inversion H
        | _ => idtac
      end; inversion H2; inversion H3; simplify_eq.
      + rewrite_op_cfgs. rewrite -H7. constructor.
      + rewrite_op_cfgs. constructor. eapply suffix_app. by symmetry.
      + destruct H6; rewrite_op_cfgs=>//.
        inversion H4.
        subst. rewrite assoc. constructor.
      + constructor.
        destruct H6; rewrite_op_cfgs=>//; auto.
        * left; eapply suffix_trans=>//.
        * by eapply suffix_common.
    - intros [[] lx] [[] ly] [[] lz]; rewrite !refine_op; simpl; intros=>//;
      match goal with
        | [H : Refine master _ ⊥ Refine master _ |- _ ] => inversion H
        | _ => idtac
      end; inversion H2; inversion H3; simplify_eq.
      + rewrite_op_cfgs. move: (suffix_app _ _ _ _ H7)=>[?|?]; rewrite_op_cfgs=>//.
      + rewrite_op_cfgs. rewrite -H7. rewrite_op_cfgs. rewrite H7. constructor.
      + destruct H6.
        * rewrite_op_cfgs=>//; last by eexists.
          inversion H4. subst. rewrite assoc. constructor.
        * rewrite (op_cfgs_suffix' ly lx)=>//.
          inversion H4. subst. rewrite assoc.
          rewrite_op_cfgs. rewrite -assoc. constructor.
      + constructor. destruct H6.
        * rewrite op_cfgs_suffix in H9=>//.
          inversion H9; left.
          { rewrite op_cfgs_suffix=>//.
            eapply suffix_trans=>//. }
          rewrite op_cfgs_suffix'=>//.
        * rewrite op_cfgs_suffix' in H9=>//.
          inversion H9.
          { left. move: (suffix_trans _ _ _ H4 H5)=>?.
            rewrite op_cfgs_suffix=>//. }
          { right. inversion H4. inversion H5.
            rewrite H6 in H7. apply suffix_app in H7.
            inversion H7; rewrite_op_cfgs=>//. }
    - intros [? ?] [? ?] ?.
      inversion H; subst; constructor.
      inversion H1; auto.
    - intros.
      inversion H1; rewrite !refine_op; try by rewrite_op_cfgs.
      + inversion H2.
        * rewrite_op_cfgs=>//.
        * rewrite op_cfgs_suffix'=>//.
          rewrite op_cfgs_suffix=>//.
    - intros.
      destruct x as [[] lx]; unfold core, refine_core; simpl.
      + rewrite -{2}(left_id_L _ _ lx). constructor.
      + constructor. by left.
    - intros.
      destruct x as [[] lx]; unfold core, refine_core;
      rewrite refine_op; simpl; by rewrite cfgs_id_merge.
    - intros.
      destruct x as [[] lx]; destruct y as [[] ly];
      rewrite refine_op; simpl; exists (Refine snapshot ly);
      intros; first inversion H1;
      rewrite /core /refine_core refine_op; simpl.
      + inversion H1. subst. rewrite_op_cfgs.
        split; [| split]=>//.
        constructor. right. by eexists _.
      + split; [|split]=>//.
        constructor. inversion H1. subst.
        left. by eexists _.
      + split; [|split]=>//.
  Qed.

  Canonical Structure refineDR : draT := DRAT refine_car refine_dra.

  Instance refine_car_empty : Empty refine_car := Refine snapshot [].

  Instance refine_discrete: CMRADiscrete (validityR (refineDR)).
  Proof. apply _. Qed.

  Definition refine_cmra := (validity (refineDR)).

  Global Instance refine_empty : Empty (refine_cmra) :=
    to_validity (refine_car_empty).

  Lemma refine_unit: UCMRAMixin (refine_cmra).
  Proof.
    split; try by constructor.
    intros [[? l] Hv HP].
    split.
    - split.
      + intros H. rewrite /empty /refine_empty in H.
        destruct H as [? [? ?]].
        simpl in H1. inversion H1=>//.
      + intros H. rewrite /empty /refine_empty.
        split.
        { constructor. }
        { split=>//. simpl. unfold refine_car_empty.
          destruct refine_view0.
          - rewrite -(right_id_L _ _ l). constructor.
          - constructor. left. apply suffix_nil. }
    - intros.
      rewrite /empty /refine_empty.
      simpl. unfold refine_car_empty.
      rewrite refine_op.
      destruct refine_view0; simpl;
        by rewrite op_cfgs_suffix; last by apply suffix_nil.
  Qed.

  Canonical Structure refine_ucmra : ucmraT :=
    (UCMRAT refine_cmra (cmra_ofe_mixin _) (cmra_mixin _) refine_unit).

End algebra.
