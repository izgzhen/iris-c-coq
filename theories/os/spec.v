(* Spec Monoid *)

Require Import iris.algebra.gmap.
Require Import iris_os.clang.lang.

Definition spec_state := gmap ident val.

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
      spec_step_star c s c' s' →
      spec_step c' s' c'' s'' →
      spec_step_star c s c'' s''.

Lemma spec_step_rel' (r: spec_rel) s retv s':
  r s retv s' → spec_step (SCrel r) s (SCdone retv) s'.
Proof.
  rewrite -{2}(left_id_L _ _ s') -{2}(left_id_L _ _ s).
  intros. apply spec_step_rel=>//.
Qed.
