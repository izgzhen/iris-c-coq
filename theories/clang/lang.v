(** Language definition **)

From iris_os.lib Require Export smap prelude.
From iris.algebra Require Export gmap.
From iris_os.clang Require Export memory types.

Open Scope Z_scope.

Inductive bop :=
| oplus
| ominus
| oequals
| oneq.

Inductive expr :=
| Evalue (v: val)
| Evar (x: ident)
| Ebinop (op: bop) (e1: expr) (e2: expr)
| Ederef (e: expr)
| Ederef_typed (t: type) (e: expr) (* not in source *)
| Eaddrof (e: expr)
| Efst (e: expr)
| Esnd (e: expr)
| Ecall (fid: ident) (args: list expr).
(* | Ecast (e: expr) (t: type) *) (* NOTE: either cast or index are not essential, we'll do it later *)

Definition tid := nat.

(* TODO: Parameterize it *)
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
| Sseq (s1 s2: stmts).
(* | Sprint (e: expr) *)
(* | Sfree *)
(* | Salloc *)

Definition decls := list (ident * type).

Definition function : Type := (type * decls * stmts).

Definition program := ident → option function.

(* Operational Semantics *)

Inductive exprctx :=
| EKid
| EKbinopr (op: bop) (re: expr)
| EKbinopl (op: bop) (lv: val)
| EKderef_typed (t: type)
| EKaddrof
| EKfst
| EKsnd
| EKcall (fid: ident) (vargs: list val) (args: list expr).
(* | EKcast (t: type) *)

Inductive stmtsctx :=
| SKassignr (rhs: expr)
| SKassignl (lhs: addr)
| SKif (s1 s2: stmts)
| SKwhile (cond: expr) (s: stmts)
| SKrete.

Definition context : Type := (exprctx * stmtsctx).

Inductive cureval :=
| curs (s: stmts) | cure (e: expr).

Record env :=
  Env {
      lenv: smap (type * addr);
      fenv: smap type
    }.

Fixpoint type_infer (ev: env) (e: expr) : option type :=
  match e with
    | Evalue v => Some (type_infer_v v)
    | Evar x => p ← sget x (lenv ev); Some (p.1)
    | Ebinop _ e1 _ => type_infer ev e1 (* FIXME *)
    | Ederef e' =>
      (match type_infer ev e' with
         | Some (Tptr t) => Some t
         | _ => None
       end)
    | Ederef_typed t _ => Some t
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
    | Ecall f args => sget f (fenv ev)
  end.

Definition fill_expr (e : expr) (Ke : exprctx) : expr :=
  match Ke with
    | EKid => e
    | EKbinopr op re => Ebinop op e re
    | EKbinopl op lv => Ebinop op (Evalue lv) e
    | EKderef_typed t => Ederef_typed t e
    | EKaddrof => Eaddrof e
    | EKfst => Efst e
    | EKsnd => Esnd e
    | EKcall f vargs args => Ecall f (map Evalue vargs ++ e :: args)
  end.

Definition fill_stmts (e : expr) (Ks : stmtsctx) : stmts :=
  match Ks with
    | SKassignr rhs => Sassign e rhs
    | SKassignl lhs => Sassign (Evalue (Vptr lhs)) e
    | SKif s1 s2 => Sif e s1 s2
    | SKwhile c s => Swhile c e s
    | SKrete => Srete e
  end.

Definition fill_ctx (e: expr) (K: context) : stmts :=
  match K with (ke, ks) => fill_stmts (fill_expr e ke) ks end.

Definition fill_ectxs := foldl fill_expr.

Definition mem := gmap addr byteval.

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

Fixpoint readbytes l bs (σ: mem) :=
  match bs with
    | byte::bs' => let '(b, o) := l in σ !! l = Some byte ∧ readbytes (b, o + 1)%nat bs' σ
    | _ => True
  end.

(* expr *can* have side-effect *)
Inductive estep : expr → expr → state → Prop :=
| ESbinop: ∀ lv rv op σ v',
             evalbop op lv rv = Some v' →
             estep (Ebinop op (Evalue lv) (Evalue rv))
                   (Evalue v')
                   σ
| ESderef_typed:
    ∀ σ l v t,
      typeof v t →
      readbytes l (encode_val v) σ →
      estep (Ederef_typed t (Evalue (Vptr l)))
            (Evalue v) σ
| ESfst:
    ∀ v1 v2 σ,
      estep (Efst (Evalue (Vpair v1 v2))) (Evalue v1) σ
| ESsnd:
    ∀ v1 v2 σ,
      estep (Esnd (Evalue (Vpair v1 v2))) (Evalue v2) σ
.

Fixpoint storebytes l bs (σ: mem) :=
  match bs with
    | byte::bs' => let '(b, o) := l in <[ l := byte ]> (storebytes (b, o + 1)%nat bs' σ)
    | _ => σ
  end.

(* Offset is ignored *)
Inductive sstep : stmts → state → stmts → state → Prop :=
| SSassign:
    ∀ l v σ,
      sstep (Sassign (Evalue (Vptr l)) (Evalue v))
            σ
            Sskip
            (storebytes l (encode_val v) σ)
| SSseq: ∀ s σ, sstep (Sseq Sskip s) σ s σ
(* | SKwhile (s: stmts). *)
| SSseq_head:
    ∀ s1 s1' s2 σ σ', sstep s1 σ s1' σ' → sstep (Sseq s1 s2) σ (Sseq s1' s2) σ'
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

Inductive assign_type_compatible : type → type → Prop :=
| assign_id: ∀ t, assign_type_compatible t t
| assign_null_ptr: ∀ t, assign_type_compatible (Tptr t) Tnull
| assign_ptr_ptr: ∀ t1 t2, assign_type_compatible (Tptr t1) (Tptr t2).

Lemma assign_preserves_size t1 t2:
  assign_type_compatible t1 t2 → sizeof t1 = sizeof t2.
Admitted.

Lemma assign_preserves_typeof t1 t2 v:
  assign_type_compatible t1 t2 → typeof v t2 → typeof v t1.
Proof.
  inversion 1=>//.
  { subst. intros. inversion H0; subst. constructor. }
  { intros. inversion H2; subst; constructor. }
Qed.
