Require Import lang.

Definition spec_state := nat. (* XXX: should be parameterized *)

Definition spec_rel := spec_state → (option val * spec_state) → Prop.

Inductive spec_code :=
| SCrel : spec_rel → spec_code.
