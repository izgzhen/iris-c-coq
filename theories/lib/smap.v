(* Simple map structure *)

Require Import iris_c.lib.prelude.
Require Import iris.prelude.base.

Definition smap (A: Type) := list (ident * A).

Definition semp {A: Type} : smap A := nil.

Fixpoint sget {A} k (m: smap A) : option A :=
  match m with
    | cons (k', v') m' => if decide (k'= k) then Some v' else sget k m'
    | _ => None
  end.

Definition sset {A: Type} k (v: A) (m: smap A) : smap A := cons (k, v) m.

Definition ssig {A: Type} k v : smap A := cons (k, v) nil.

Arguments sget {_} _ _.
Arguments sset {_} _ _ _.
Arguments ssig {_} _ _.
