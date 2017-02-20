(** Language definition **)

From iris.algebra Require Export gmap.
Require Export memory.
Require Export lib.Integers.
Open Scope Z_scope.

(* High-level value *)
Inductive val : Set :=
| Vnull
| Vint8 (i: int8)
| Vint32 (i: int32)
| Vptr (p: addr).

Inductive type : Set :=
| Tnull
| Tvoid
| Tint8
| Tint32
| Tptr (t: type).

Fixpoint sizeof (t : type) : nat :=
  match t with
    | Tnull => 4 %nat
    | Tvoid => 0 % nat
    | Tint8 => 1 % nat
    | Tint32 => 4 % nat
    | Tptr _ => 4 % nat
  end.

Inductive typeof : type → val → Prop :=
| typeof_null: typeof Tnull Vnull
| typeof_int8_to_int32:
    ∀ v: int32, (Int.unsigned v) <=? Byte.max_unsigned → typeof Tint8 (Vint32 v)
| typeof_int8: ∀ i, typeof Tint8 (Vint8 i)
| typeof_int32: ∀ i, typeof Tint32 (Vint32 i)
| typeof_ptr: ∀ t l, typeof (Tptr t) (Vptr l).

Inductive bop:=
| oplus
| ominus.

(* Encoding and decoding for values *)
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

Definition encode_val (t: type) (v: val) : list byteval :=
  match v, t with
  | Vint32 n, Tint8  => inj_bytes (encode_int 1%nat (Int.unsigned n))
  | Vint32 n, Tint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
  | Vptr p, Tptr _ => inj_pointer 4%nat p
  | Vnull, Tnull => list_repeat 4 BVnull
  | Vnull, Tptr _ => list_repeat 4 BVnull
  | _, _ => list_repeat (sizeof t) BVundef
  end.

Definition decode_val (t: type) (vl: list byteval) : option val :=
  match proj_bytes vl with
  | Some bl =>
      match t with
      | Tint8  => Some (Vint32 (Int.zero_ext 8 (Int.repr (decode_int bl))))
      | Tint32 => Some (Vint32 (Int.repr (decode_int bl)))
      | _ => None
      end
  | None =>
    match vl with
      | BVnull :: BVnull ::BVnull :: BVnull :: nil =>
        match t with
          | Tnull => Some Vnull
          | Tptr _ => Some Vnull
          | _ => None
        end
      | _ =>
        match t with
          | Tptr _ => proj_pointer vl
          | _ => None
        end
    end
  end.

Definition ident := Z.

Inductive expr :=
 | Evalue (v: val)
 | Evar (x: ident)
 | Ebinop (op: bop) (e1: expr) (e2: expr)
 | Ederef (e: expr)
 | Eaddrof (e: expr)
 (* | Efield (e: expr) *)
 | Ecast (e: expr) (t: type).
 (* | Eindex (e: expr) (e: expr). *)

Inductive stmts :=
| Sskip
| Sassign (lhs: expr) (rhs: expr)
| Sif (cond: expr) (s1 s2: stmts)
| Swhile (cond: expr) (s: stmts)
(* | Sret *)
(* | Srete (e: expr) *)
(* | Scall (fid: ident) (args: list expr) *)
(* | Scalle (lhs: expr) (fid: ident) (args: list expr) *)
| Sseq (s1 s2: stmts).
(* | Sprint (e: expr) *)
(* | Sfree *)
(* | Salloc *)

Notation "S1 ';;;' S2" := (Sseq S1 S2) (at level 97, right associativity, format "S1 ';;;' S2").

(* Definition decls := list (ident * type). *)

(* Definition function : Set := (type * decls * decls * stmts). *)

(* Definition program := ident → option function. *)

(* Operational Semantics *)

Inductive cureval :=
| cure (e: expr)
| curs (s: stmts).

Inductive exprctx :=
| EKbinopr (op: bop) (re: expr)
| EKbinopl (op: bop) (lv: val)
| EKderef
| EKaddrof
| EKcast (t: type).

Inductive stmtsctx :=
| SKassignr (rhs: expr)
| SKassignl (lhs: addr)
| SKif (s1 s2: stmts)
| SKwhile (s: stmts).
(* | SKrete *)
(* | SKcall (fid: ident) (vargs: list val) (args: list expr) *)
(* | SKcaller (fid: ident) (args: list expr) *)
(* | SKcallel (lhs: addr) (fid: ident) (vargs: list val) (args: list expr) (args: list expr). *)

Definition exprcont := list exprctx.
Definition stmtscont := list stmtsctx.
Definition cont : Set := (exprcont * stmtscont).
Definition code : Set := (cureval * cont).

Definition knil : cont := ([], []).

Definition fill_expr (Ke : exprctx) (e : expr) : expr :=
  match Ke with
    | EKbinopr op re => Ebinop op e re
    | EKbinopl op lv => Ebinop op (Evalue lv) e
    | EKderef => Ederef e
    | EKaddrof => Eaddrof e
    | EKcast t => Ecast e t
  end.

Definition fill_stmts (Ks : stmtsctx) (e : expr) : stmts :=
  match Ks with
    | SKassignr rhs => Sassign e rhs
    | SKassignl lhs => Sassign (Evalue (Vptr lhs)) e
    | SKif s1 s2 => Sif e s1 s2
    | SKwhile s => Swhile e s
  end.

Definition mem := gmap block (list byteval).

Definition state := mem.

Definition to_val (c: code) : option val :=
  match c with
    | (cure (Evalue v), knil) => Some v
    | _ => None
  end.

Definition of_val (v: val) : code := (cure (Evalue v), knil).

Definition reducible (c: code) : Prop :=
  match c with
    | (cure (Evalue v), knil) => True
    | (curs Sskip, knil) => True
    | _ => False
  end.

(* XXX: not precise *)
Definition evalbop (op: bop) v1 v2 : option val :=
  match op with
    | oplus => (match v1, v2 with
                  | Vint8 i1, Vint8 i2 => Some (Vint8 (Byte.add i1 i2))
                  | Vint32 i1, Vint32 i2 => Some (Vint32 (Int.add i1 i2))
                  | _, _ => None
               end)
    | ominus => None
  end.

Inductive estep : cureval → exprcont → cureval → exprcont → state → Prop :=
| ESbinop: ∀ lv rv op ke σ v',
             evalbop op lv rv = Some v' →
             estep (cure (Evalue rv))
                   (EKbinopl op lv :: ke)
                   (cure (Evalue v')) ke σ
(* | EKderef *)
(* | ekaddrof *)
(* | EKcast (t: type). *)
.

(* Offset is ignored *)
Inductive sstep : cureval → stmtscont → state → cureval → stmtscont → state → Prop :=
| SSassign:
    ∀ t rv bytes bytes' σ b off ks,
      typeof t rv →
      encode_val t rv = bytes' →
      σ !! b = Some bytes →
      sstep (cure (Evalue rv))
            (SKassignl (b, off) :: ks) σ
            (curs Sskip) ks
            (<[ b := take off bytes ++ take (length bytes - off) bytes' ]> σ)
(* | SKif (s1 s2: stmts) *)
(* | SKwhile (s: stmts). *)
.

Inductive head_step : code → state → code → state → Prop :=
| head_estep:
    ∀ c c' ke ke' ks σ,
      estep c ke c' ke' σ →
      head_step (c, (ke, ks)) σ (c', (ke', ks)) σ
| head_sstep:
    ∀ c c' ks ks' ke σ σ',
      sstep c ks σ c' ks' σ' →
      head_step (c, (ke, ks)) σ (c', (ke, ks')) σ'.
