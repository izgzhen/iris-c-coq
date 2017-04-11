(* Spec Monoid *)

Require Import iris.algebra.gmap.
Require Import iris_os.clang.lang.

Definition spec_state := gmap ident val. (* XXX: should be parameterized *)

Definition spec_rel := spec_state → option val → spec_state → Prop.

Inductive spec_code :=
| SCrel (r: spec_rel)
| SCdone (v: option val).

Inductive spec_step : spec_code → spec_state → spec_code → spec_state → Prop :=
| spec_step_rel:
    ∀ (r: spec_rel) s retv s' sf,
      gset_dom sf ⊥ gset_dom s → r s retv s' →
      spec_step (SCrel r) (sf ∪ s) (SCdone retv) (sf ∪ s').

Inductive spec_step_star: spec_code → spec_state → spec_code → spec_state → Prop :=
| SSid: ∀ c s, spec_step_star c s c s
| SStrans:
    ∀ c c' c'' s s' s'',
      spec_step_star c s c' s' → spec_step c' s' c'' s'' → spec_step_star c s c'' s''.

Lemma left_id_ss  (s' : spec_state):
  ∅ ∪ s' = s'.
Admitted.

Lemma spec_step_rel' (r: spec_rel) s retv s':
  r s retv s' → spec_step (SCrel r) s (SCdone retv) s'.
Proof.
  rewrite -{2}(left_id_ss s') -{2}(left_id_ss s).
  intros. apply spec_step_rel=>//.
Qed.

Lemma union_assoc_disj (s1 s2 s: spec_state):
  gset_dom s1 ⊥ gset_dom s2 → s1 ∪ (s2 ∪ s) = (s1 ∪ s2) ∪ s.
Admitted.

Lemma union_disj (sf sf0 s0: spec_state):
  gset_dom sf ⊥ gset_dom (sf0 ∪ s0) → gset_dom sf ⊥ gset_dom sf0.
Admitted.

Lemma foo (sf0 s0 sf: spec_state):
  gset_dom sf0 ⊥ gset_dom s0 →
  gset_dom sf ⊥ gset_dom (sf0 ∪ s0) →
  gset_dom (sf ∪ sf0) ⊥ gset_dom s0.
Admitted.

Lemma spec_step_framing c c' sf s s':
  gset_dom sf ⊥ gset_dom s → spec_step c s c' s' → spec_step c (sf ∪ s) c' (sf ∪ s').
Proof.
  inversion 2. subst.
  rewrite union_assoc_disj=>//; last by eapply union_disj.
  rewrite union_assoc_disj=>//; last by eapply union_disj.
  by constructor; first by apply foo.
Qed.

(* Naive equivalence *)
Instance spec_code_equiv: Equiv spec_code := (=).
