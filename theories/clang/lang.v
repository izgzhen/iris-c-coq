(** Language definition **)

From iris.algebra Require Export gmap.
Require Export memory.
From iris_os.lib Require Export Integers.
Open Scope Z_scope.

Definition ident := Z.

Inductive type : Set :=
| Tnull
| Tvoid
| Tint8
| Tint32
| Tptr (t: type)
| Tprod (t1 t2: type).

(* High-level value *)
Inductive val : Set :=
| Vvoid
| Vnull
| Vint8 (i: int8)
| Vint32 (i: int32)
| Vptr (p: addr)
| Vpair (v1 v2: val).

Instance int_eq_dec : EqDecision int.
Proof. apply Int.eq_dec. Defined.

Instance byte_eq_dec : EqDecision byte.
Proof. apply Byte.eq_dec. Defined.

Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Definition vtrue := Vint8 (Byte.repr 1).
Definition vfalse := Vint8 (Byte.repr 0).

Fixpoint sizeof (t : type) : nat :=
  match t with
    | Tnull => 4 %nat
    | Tvoid => 0 % nat
    | Tint8 => 1 % nat
    | Tint32 => 4 % nat
    | Tptr _ => 4 % nat
    | Tprod t1 t2 => sizeof t1 + sizeof t2
  end.

Inductive typeof : type → val → Prop :=
| typeof_void: typeof Tvoid Vvoid
| typeof_null: typeof Tnull Vnull
| typeof_null_ptr: ∀ t, typeof (Tptr t) Vnull
| typeof_int32_to_int8:
    ∀ v: int32, (Int.unsigned v) <=? Byte.max_unsigned → typeof Tint8 (Vint32 v)
| typeof_int8_to_int32: ∀ v: int8, typeof Tint32 (Vint8 v)
| typeof_int8: ∀ i, typeof Tint8 (Vint8 i)
| typeof_int32: ∀ i, typeof Tint32 (Vint32 i)
| typeof_ptr: ∀ t l, typeof (Tptr t) (Vptr l)
| typeof_prod: ∀ t1 t2 v1 v2, typeof t1 v2 → typeof t2 v2 → typeof (Tprod t1 t2) (Vpair v1 v2).

Inductive bop:=
| oplus
| ominus
| oequals
| oneq.

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

Fixpoint encode_val (t: type) (v: val) : list byteval :=
  match v, t with
    | Vint32 n, Tint8  => inj_bytes (encode_int 1%nat (Int.unsigned n))
    | Vint32 n, Tint32 => inj_bytes (encode_int 4%nat (Int.unsigned n))
    | Vptr p, Tptr _ => inj_pointer 4%nat p
    | Vnull, Tnull => list_repeat 4 BVnull
    | Vnull, Tptr _ => list_repeat 4 BVnull
    | Vpair v1 v2, Tprod t1 t2 => encode_val t1 v1 ++ encode_val t1 v2
    | _, _ => list_repeat (sizeof t) BVundef
  end.

Fixpoint decode_val (t: type) (vl: list byteval) : option val :=
  match t with
    | Tprod t1 t2 =>
      (match decode_val t1 (take (sizeof t1) vl),
             decode_val t2 (drop (sizeof t1) vl) with
         | Some v1, Some v2 => Some (Vpair v1 v2)
         | _, _ => None
       end)
    | _ =>
      (match proj_bytes vl with
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
       end)
  end.

Inductive expr :=
| Evalue (v: val)
| Evar (x: ident)
| Ebinop (op: bop) (e1: expr) (e2: expr)
| Ederef (e: expr)
| Eaddrof (e: expr)
| Efst (e: expr)
| Esnd (e: expr)
| Ecast (e: expr) (t: type).
(* | Eindex (e: expr) (e: expr). *)

Definition tid := nat.

Inductive prim :=
| Pcli | Psti | Pswitch (i: tid).

Inductive stmts :=
| Sskip
| Sprim (p: prim)
| Sassign (lhs: expr) (rhs: expr)
| Sif (cond: expr) (s1 s2: stmts)
| Swhile (cond: expr) (curcond: expr) (s: stmts)
| Sret
| Srete (e: expr)
| Scall (fid: ident) (args: list expr)
(* | Scalle (lhs: expr) (fid: ident) (args: list expr) *)
| Sseq (s1 s2: stmts).
(* | Sprint (e: expr) *)
(* | Sfree *)
(* | Salloc *)

Definition decls := list (ident * type).

Definition function : Type := (type * decls * stmts).
(* (type * decls * decls * stmts). *) (* no local vars *)

Definition program := ident → option function.

(* Operational Semantics *)

Inductive exprctx :=
| EKid
| EKbinopr (op: bop) (re: expr)
| EKbinopl (op: bop) (lv: val)
| EKderef
| EKaddrof
| EKfst
| EKsnd
| EKcast (t: type).

Inductive stmtsctx :=
| SKassignr (rhs: expr)
| SKassignl (lhs: addr)
| SKif (s1 s2: stmts)
| SKwhile (cond: expr) (s: stmts)
| SKrete
| SKcall (fid: ident) (vargs: list val) (args: list expr).
(* | SKcaller (fid: ident) (args: list expr) *)
(* | SKcallel (lhs: addr) (fid: ident) (vargs: list val) (args: list expr) (args: list expr). *)

Definition context : Type := (exprctx * stmtsctx).

Inductive cureval :=
| curs (s: stmts) | cure (e: expr).

Definition env : Type := gmap ident (type * addr).

Fixpoint type_infer_v (v: val) : type :=
  match v with
    | Vnull => Tnull
    | Vvoid => Tvoid
    | Vint8 _ => Tint8
    | Vint32 _ => Tint32
    | Vptr _ => Tptr Tvoid (* XXX *)
    | Vpair v1 v2 => Tprod (type_infer_v v1) (type_infer_v v2)
  end.

Fixpoint type_infer (ev: env) (e: expr) : option type :=
  match e with
    | Evalue v => Some (type_infer_v v)
    | Evar x => p ← ev !! x; Some (p.1)
    | Ebinop _ e1 _ => type_infer ev e1 (* FIXME *)
    | Ederef e' =>
      (match type_infer ev e' with
         | Some (Tptr t) => Some t
         | _ => None
       end)
    | Eaddrof e' => Tptr <$> type_infer ev e'
    | Efst e' =>
      (match type_infer ev e' with
         | Some (Tprod t1 _) => Some t1
         | _ => None
       end)
    | Esnd e' =>
      (match type_infer ev e' with
         | Some (Tprod _ t2) => Some t2
         | _ => None
       end)
    | Ecast _ t => Some t (* FIXME *)
  end.

Definition code : Type := (cureval * context * list context).

Definition fill_expr (e : expr) (Ke : exprctx) : expr :=
  match Ke with
    | EKid => e
    | EKbinopr op re => Ebinop op e re
    | EKbinopl op lv => Ebinop op (Evalue lv) e
    | EKderef => Ederef e
    | EKaddrof => Eaddrof e
    | EKfst => Efst e
    | EKsnd => Esnd e
    | EKcast t => Ecast e t
  end.

Definition fill_stmts (e : expr) (Ks : stmtsctx) : stmts :=
  match Ks with
    | SKassignr rhs => Sassign e rhs
    | SKassignl lhs => Sassign (Evalue (Vptr lhs)) e
    | SKif s1 s2 => Sif e s1 s2
    | SKwhile c s => Swhile c e s
    | SKcall f vargs args => Scall f (map Evalue vargs ++ e :: args)
    | SKrete => Srete e
  end.

Definition fill_ctx (e: expr) (K: context) : stmts :=
  match K with (ke, ks) => fill_stmts (fill_expr e ke) ks end.

Definition fill_ectxs := foldl fill_expr.

Definition mem := gmap block (list byteval).

Definition state := mem.

Definition offset_by_int32 (o: nat) (i: int32) : nat := o + Z.to_nat (Int.intval i).
Definition offset_by_byte (o: nat) (i: byte) : nat := o + Z.to_nat (Byte.intval i).

(* XXX: not precise *)
Definition evalbop (op: bop) v1 v2 : option val :=
  match op with
    | oplus => (match v1, v2 with
                  | Vint8 i1, Vint8 i2 => Some (Vint8 (Byte.add i1 i2))
                  | Vint32 i1, Vint32 i2 => Some (Vint32 (Int.add i1 i2))
                  | Vint8 i, Vptr (b, o) => Some (Vptr (b, offset_by_byte o i))
                  | Vint32 i, Vptr (b, o) => Some (Vptr (b, offset_by_int32 o i))
                  | Vptr (b, o), Vint8 i => Some (Vptr (b, offset_by_byte o i))
                  | Vptr (b, o), Vint32 i => Some (Vptr (b, offset_by_int32 o i))
                  | _, _ => None
                end)
    | ominus => (match v1, v2 with
                  | Vint8 i1, Vint8 i2 => Some (Vint8 (Byte.sub i1 i2))
                  | Vint32 i1, Vint32 i2 => Some (Vint32 (Int.sub i1 i2))
                  | _, _ => None
                 end)
    | oequals => if decide (v1 = v2) then Some vtrue else Some vfalse
    | oneq => if decide (v1 = v2) then Some vfalse else Some vtrue
  end.

(* expr *can* have side-effect *)
Inductive estep : expr → expr → state → Prop :=
| ESbinop: ∀ lv rv op σ v',
             evalbop op lv rv = Some v' →
             estep (Ebinop op (Evalue lv) (Evalue rv))
                   (Evalue v')
                   σ
(* | EKderef *)
(* | ekaddrof *)
(* | EKcast (t: type). *)
.

(* Offset is ignored *)
Inductive sstep : stmts → state → stmts → state → Prop :=
| SSassign:
    ∀ t rv bytes bytes' σ b off,
      typeof t rv →
      encode_val t rv = bytes' →
      σ !! b = Some bytes →
      sstep (Sassign (Evalue (Vptr (b, off))) (Evalue rv))
            σ
            Sskip
            (<[ b := take off bytes ++ take (length bytes - off) bytes' ]> σ)
(* | SKif (s1 s2: stmts) *)
(* | SKwhile (s: stmts). *)
.

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.
Bind Scope stmts_scope with stmts.
Delimit Scope stmts_scope with S.
Bind Scope prim_scope with prim.
Delimit Scope prim_scope with prim.

Definition to_val (c: cureval) :=
  match c with
    | cure (Evalue v) => Some v
    | curs Sskip => Some Vvoid
    | _ => None
  end.

Lemma of_to_val e v : to_val (cure e) = Some v → e = Evalue v.
Admitted.

Definition to_ret_val (c: cureval) :=
  match c with
    | curs Sret => Some Vvoid
    | curs (Srete (Evalue v)) => Some v
    | _ => None
  end.

Lemma fill_not_val Kes Ks e: to_val (curs (fill_stmts (fill_ectxs e Kes) Ks)) = None.
Admitted.

Lemma fill_not_ret_val Kes Ks e: to_ret_val (curs (fill_stmts (fill_ectxs e Kes) Ks)) = None.
Admitted.

Lemma val_implies_not_ret_val c v:
  to_val c = Some v → to_ret_val c = None.
Proof. intros ?. destruct c as [[]|[]]=>//. Qed.

Lemma ret_val_implies_not_val c v:
  to_ret_val c = Some v → to_val c = None.
Proof. intros ?. destruct c as [[]|[]]=>//. Qed.

(* Definition to_val (e: expr) := *)
(*   match e with *)
(*     | Evalue v => Some v *)
(*     | _ => None *)
(*   end. *)

(* Definition of_val (v: val) := Evalue v. *)

Inductive cstep: cureval → state → cureval → state → Prop :=
| CSestep: ∀ e e' σ, estep e e' σ → cstep (cure e) σ (cure e') σ
| CSsstep: ∀ s s' σ σ', sstep s σ s' σ' → cstep (curs s) σ (curs s') σ'.

Lemma fill_step_inv σ σ' e c' Kes Ks:
  to_val (cure e) = None →
  to_ret_val (cure e) = None →
  cstep (curs (fill_stmts (fill_ectxs e Kes) Ks)) σ c' σ' →
  (∃ e', c' = curs (fill_stmts (fill_ectxs e' Kes) Ks) ∧ estep e e' σ ∧ σ = σ').
Admitted.

Definition reducible cur σ := ∃ cur' σ', cstep cur σ cur' σ'.

Lemma lift_reducible e Kes Ks σ:
  reducible (cure e) σ → reducible (curs(fill_stmts (fill_ectxs e Kes) Ks)) σ.
Admitted.

Lemma reducible_not_val c σ: reducible c σ → to_val c = None.
Admitted.

Lemma reducible_not_ret_val c σ: reducible c σ → to_ret_val c = None.
Admitted.

Instance state_inhabited: Inhabited state := populate ∅.
