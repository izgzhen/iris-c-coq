From iris_os.clang Require Import memory.

Inductive type : Set :=
| Tnull
| Tvoid
| Tint8
| Tint32
| Tptr (t: type)
| Tprod (t1 t2: type).

Instance equiv_type: Equiv type := (=).

Fixpoint type_infer_v (v: val) : type :=
  match v with
    | Vnull => Tnull
    | Vvoid => Tvoid
    | Vint8 _ => Tint8
    | Vint32 _ => Tint32
    | Vptr _ => Tptr Tvoid (* XXX *)
    | Vpair v1 v2 => Tprod (type_infer_v v1) (type_infer_v v2)
  end.

Inductive typeof: val → type → Prop :=
| typeof_null: typeof Vnull Tnull
| typeof_void: typeof Vvoid Tvoid
| typeof_int8: ∀ i, typeof (Vint8 i) Tint8
| typeof_int32: ∀ i, typeof (Vint32 i) Tint32
| typeof_prod:
    ∀ v1 v2 t1 t2,
      typeof v1 t1 → typeof v2 t2 → typeof (Vpair v1 v2) (Tprod t1 t2)
| typeof_null_ptr: ∀ t, typeof Vnull (Tptr t)
| typeof_ptr: ∀ l t, typeof (Vptr l) (Tptr t).

Lemma null_typeof v: typeof v Tnull → v = Vnull. Proof. induction v; inversion 1=>//. Qed.
Lemma void_typeof v: typeof v Tvoid → v = Vvoid. Proof. induction v; inversion 1=>//. Qed.
Lemma int8_typeof v: typeof v Tint8 → (∃ i, v = Vint8 i). Proof. induction v; inversion 1=>//. eauto. Qed.
Lemma int32_typeof v: typeof v Tint32 → (∃ i, v = Vint32 i). Proof. induction v; inversion 1=>//. eauto. Qed.

Lemma typeof_any_ptr l t1 t2:
  typeof l (Tptr t1) → typeof l (Tptr t2).
Proof. induction l; inversion 1; subst=>//; constructor. Qed.

Instance sizeof_type: Sizeof type :=
  fix go (t : type) : nat :=
  match t with
    | Tnull => 4 %nat
    | Tvoid => 0 % nat
    | Tint8 => 1 % nat
    | Tint32 => 4 % nat
    | Tptr _ => 4 % nat
    | Tprod t1 t2 => go t1 + go t2
  end.

Lemma typeof_preserves_size v t:
  typeof v t → sizeof t = length (encode_val v).
Admitted.

Lemma type_infer_preserves_size v:
  sizeof (type_infer_v v) = length (encode_val v).
Admitted.

(* Fixpoint decode_val (t: type) (vl: list byteval) : option val := *)
(*   match t with *)
(*     | Tprod t1 t2 => *)
(*       (match decode_val t1 (take (sizeof t1) vl), *)
(*              decode_val t2 (drop (sizeof t1) vl) with *)
(*          | Some v1, Some v2 => Some (Vpair v1 v2) *)
(*          | _, _ => None *)
(*        end) *)
(*     | _ => *)
(*       (match proj_bytes vl with *)
(*          | Some bl => *)
(*            match t with *)
(*              | Tint8  => Some (Vint32 (Int.zero_ext 8 (Int.repr (decode_int bl)))) *)
(*              | Tint32 => Some (Vint32 (Int.repr (decode_int bl))) *)
(*              | _ => None *)
(*            end *)
(*          | None => *)
(*            match vl with *)
(*              | BVnull :: BVnull ::BVnull :: BVnull :: nil => *)
(*                match t with *)
(*                  | Tnull => Some Vnull *)
(*                  | Tptr _ => Some Vnull *)
(*                  | _ => None *)
(*                end *)
(*              | _ => *)
(*                match t with *)
(*                  | Tptr _ => proj_pointer vl *)
(*                  | _ => None *)
(*                end *)
(*            end *)
(*        end) *)
(*   end. *)
