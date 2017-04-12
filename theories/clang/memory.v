(** Definition of the physical memory model **)
Require Export lib.Coqlib.
Require Export Integers.
Require Export iris.base_logic.base_logic.

Open Local Scope Z_scope.

Class Sizeof C := sizeof: C → nat.

Arguments sizeof _ _ _ /.
Typeclasses Transparent sizeof.

Definition block : Set := positive.
Definition offset := nat.
Definition addr : Set := prod block offset.

Definition shift_loc l (o: nat) : addr :=
  let '(b, o') := l in (b, o' + o)%nat.

Instance addr_eq_dec : EqDecision addr.
Proof. solve_decision. Defined.
Instance int_eq_dec : EqDecision int.
Proof. apply Int.eq_dec. Defined.
Instance byte_eq_dec : EqDecision byte.
Proof. apply Byte.eq_dec. Defined.

(* Byte-level value *)
Inductive byteval : Set :=
| BVundef
| BVint8 (i: int8)
| BVaddr (p: addr) (k: nat)
| BVnull.

(* High-level value *)
Inductive val : Set :=
| Vvoid
| Vnull
| Vint8 (i: int8)
| Vint32 (i: int32)
| Vptr (p: addr)
| Vpair (v1 v2: val).


Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Global Instance val_equiv: Equiv val := (=).

Instance sizeof_val: Sizeof val :=
  fix go v :=
  match v with
    | Vnull => 4 %nat
    | Vvoid => 0 % nat
    | Vint8 _ => 1 % nat
    | Vint32 _ => 4 % nat
    | Vptr _ => 4 % nat
    | Vpair v1 v2 => (go v1 + go v2)%nat
  end.

Definition vtrue := Vint8 (Byte.repr 1).
Definition vfalse := Vint8 (Byte.repr 0).

Definition b_to_v (b: bool) := if b then vtrue else vfalse.

(** Encoding high-level value to byte-level values **)

Fixpoint encode_int (n: nat) (x: Z): list byte :=
  match n with
    | O => nil
    | S m => Byte.repr x :: encode_int m (x / 256)
  end.

Fixpoint decode_int (l: list byte): Z :=
  match l with
    | nil => 0
    | b :: l' => Byte.unsigned b + decode_int l' * 256
  end.

Lemma encode_int_length:
  forall sz x, length(encode_int sz x) = sz.
Proof.
  induction sz; simpl; intros. auto. decEq. auto.
Qed.

Definition inj_bytes (bl: list byte) : list byteval := List.map BVint8 bl.

Fixpoint proj_bytes (vl: list byteval) : option (list byte) :=
  match vl with
    | nil => Some nil
    | BVint8 b :: vl' =>
      match proj_bytes vl' with None => None | Some bl => Some (b :: bl) end
    | _ => None
  end.

Lemma length_inj_bytes:
  forall bl, length (inj_bytes bl) = length bl.
Proof.
  intros. apply List.map_length.
Qed.

Lemma proj_inj_bytes:
  forall bl, proj_bytes (inj_bytes bl) = Some bl.
Proof.
  induction bl; simpl. auto. rewrite IHbl. auto.
Qed.

Lemma inj_proj_bytes:
  forall cl bl, proj_bytes cl = Some bl -> cl = inj_bytes bl.
Proof.
  induction cl; simpl; intros.
  inv H; auto.
  destruct a; try congruence. destruct (proj_bytes cl); inv H.
  simpl. decEq. auto.
Qed.

Fixpoint inj_pointer (n: nat) (p: addr): list byteval :=
  match n with
    | O => nil
    | S n => BVaddr p n :: inj_pointer n p
  end.

Fixpoint check_pointer (n: nat) (p: addr) (vl: list byteval) : bool :=
  match n, vl with
    | O, nil => true
    | S m, BVaddr p' m' :: vl' =>
      bool_decide (p = p') && beq_nat m m' && check_pointer m p vl'
    | _, _ => false
  end.

Definition proj_pointer (vl: list byteval) : option val :=
  match vl with
    | BVaddr p n :: vl' =>
      if check_pointer 4%nat p vl then Some (Vptr p) else None
    | _ => None
  end.

Fixpoint encode_val (v: val) : list byteval :=
  match v with
    | Vint32 n => inj_bytes (encode_int 4%nat (Int.unsigned n))
    | Vint8 n => inj_bytes (encode_int 1%nat (Byte.unsigned n))
    | Vptr p => inj_pointer 4%nat p
    | Vnull => list_repeat 4 BVnull
    | Vpair v1 v2 => encode_val v1 ++ encode_val v2
    | _ => list_repeat (sizeof v) BVundef
  end.


Lemma size_of_encode_val v:
  length (encode_val v) = sizeof v.
Proof. simpl. induction v=>//. rewrite app_length. simpl. omega. Qed.
