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

Definition decls := list (ident * type).

Definition tid := nat.

(* TODO: Parameterize it *)
Inductive prim :=
| Pcli | Psti | Pswitch (i: tid).

Inductive expr :=
| Evalue (v: val)
| Evar (x: ident)
| Ebinop (op: bop) (e1: expr) (e2: expr)
| Ederef (e: expr)
| Ederef_typed (t: type) (e: expr) (* not in source *)
| Eaddrof (e: expr)
| Efst (e: expr)
| Esnd (e: expr)
| Ecall (fid: ident) (args: list expr)
| Ealloc (t: type) (e: expr)
| Eassign (lhs: expr) (rhs: expr)
| Eif (cond: expr) (s1 s2: expr)
| Ewhile (cond: expr) (curcond: expr) (s: expr)
| Erete (e: expr)
| Eseq (s1 s2: expr).

Record function :=
  Function {
      f_retty: type;
      f_params: decls;
      f_body: expr
    }.

(* Operational Semantics *)

Inductive exprctx :=
| EKbinopr (op: bop) (re: expr)
| EKbinopl (op: bop) (lv: val)
| EKderef_typed (t: type)
| EKaddrof
| EKfst
| EKsnd
| EKcall (fid: ident) (vargs: list val) (args: list expr)
| EKalloc (t: type)
| EKassignr (rhs: expr)
| EKassignl (lhs: addr)
| EKif (s1 s2: expr)
| EKwhile (cond: expr) (s: expr)
| EKrete
| EKseq (s: expr).

Record env :=
  Env {
      lenv: smap (type * addr);
      fenv: smap function
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
    | Ecall f args => f_retty <$> sget f (fenv ev)
    | Ealloc t _ => Some (Tptr t)
    | _ => Some Tvoid
  end.

Definition fill_expr (e : expr) (Ke : exprctx) : expr :=
  match Ke with
    | EKbinopr op re => Ebinop op e re
    | EKbinopl op lv => Ebinop op (Evalue lv) e
    | EKderef_typed t => Ederef_typed t e
    | EKaddrof => Eaddrof e
    | EKfst => Efst e
    | EKsnd => Esnd e
    | EKcall f vargs args => Ecall f (map Evalue vargs ++ e :: args)
    | EKalloc t => Ealloc t e
    | EKassignr rhs => Eassign e rhs
    | EKassignl lhs => Eassign (Evalue (Vptr lhs)) e
    | EKif s1 s2 => Eif e s1 s2
    | EKwhile c s => Ewhile c e s
    | EKrete => Erete e
    | EKseq s => Eseq (Evalue Vvoid) s
  end.


Definition fill_ectxs := foldl fill_expr.

Definition heap := gmap addr byteval.
Definition text := gmap ident function.

Record state :=
  State {
      s_heap : heap;
      s_text : text
    }.

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

Fixpoint readbytes l bs (σ: heap) :=
  match bs with
    | byte::bs' => let '(b, o) := l in σ !! l = Some byte ∧ readbytes (b, o + 1)%nat bs' σ
    | _ => True
  end.

Fixpoint storebytes l bs (σ: heap) :=
  match bs with
    | byte::bs' => let '(b, o) := l in <[ l := byte ]> (storebytes (b, o + 1)%nat bs' σ)
    | _ => σ
  end.

Definition alloc_heap (l: addr) (v: val) (σ: state) : state :=
  State (storebytes l (encode_val v) (s_heap σ)) (s_text σ).

(* expr *can* have side-effect *)

Definition to_val (c: expr) :=
  match c with
    | Evalue v => Some v
    | _ => None
  end.

Lemma of_to_val e v : to_val e = Some v → e = Evalue v.
Proof. induction e; crush. Qed.

Lemma fill_ectx_not_val e K: to_val (fill_expr e K) = None.
Proof. induction K; crush. Qed.

Lemma fill_ectxs_not_val Kes: ∀ e, to_val e = None → to_val (fill_ectxs e Kes) = None.
Proof. induction Kes; first by inversion 1.
       intros. simpl. apply IHKes. apply fill_ectx_not_val. Qed.

Fixpoint params_match (params: decls) (vs: list val) :=
  match params, vs with
    | (_, t)::params, v::vs => typeof v t ∧ params_match params vs
    | [], [] => True
    | _, _ => False
  end.

Fixpoint lift_list_option {A} (l: list (option A)): option (list A) :=
  match l with
    | Some x :: l' => (x ::) <$> lift_list_option l'
    | None :: _ => None
    | _ => Some []
  end.

Fixpoint resolve_rhs (ev: env) (e: expr) : option expr :=
  match e with
    | Evalue v => Some e
    | Ederef_typed t e => Some e
    | Ealloc t e => Ealloc t <$> resolve_rhs ev e
    | Evar x => (* closed-ness? *)
      (match sget x (lenv ev) with
         | Some (t, l) => Some $ Ederef_typed t (Evalue (Vptr l))
         | None => None
       end)
    | Ebinop op e1 e2 =>
      match resolve_rhs ev e1, resolve_rhs ev e2 with
        | Some e1', Some e2' => Some (Ebinop op e1' e2')
        | _, _ => None
      end
    | Ederef e =>
      match type_infer ev e, resolve_rhs ev e with
        | Some (Tptr t), Some e' => Some (Ederef_typed t e') 
        | _, _ => None
      end
    | Eaddrof e => Eaddrof <$> resolve_rhs ev e
    | Efst e => Efst <$> resolve_rhs ev e
    | Esnd e => Esnd <$> resolve_rhs ev e
    | Ecall f args => Ecall f <$> lift_list_option (map (resolve_rhs ev) args)
    | Eassign e1 e2 => Eassign e1 <$> resolve_rhs ev e2
    | Eif e s1 s2 =>
      match resolve_rhs ev e, resolve_rhs ev s1, resolve_rhs ev s2 with
        | Some e', Some s1', Some s2' => Some $ Eif e' s1' s2'
        | _, _, _ => None
      end
    | Ewhile c e s =>
      match resolve_rhs ev c, resolve_rhs ev e, resolve_rhs ev s with
        | Some c', Some e', Some s' => Some $ Ewhile c' e' s'
        | _, _, _ => None
      end
    | Erete e => Erete <$> resolve_rhs ev e
    | Eseq s1 s2 =>
      match resolve_rhs ev s1, resolve_rhs ev s2 with
        | Some s1', Some s2' => Some (Eseq s1' s2')
        | _, _ => None
      end
  end.

Fixpoint resolve_lhs (ev: env) (e: expr) : option expr :=
  match e with
    | Evalue (Vptr l) => Some e
    | Evalue _ => None
    | Ebinop _ _ _ => None (* XXX: too restrictive *)
    | Ederef_typed _ _ => None
    | Eaddrof _ => None
    | Ealloc _ _ => None
    | Evar x =>
      (match sget x (lenv ev) with
         | Some (_, l) => Some (Evalue (Vptr l))
         | None => None
       end)
    | Ederef e' => resolve_rhs ev e'
    | Efst e' => resolve_lhs ev e'
    | Esnd e' =>
      (e'' ← resolve_lhs ev e';
       match type_infer ev e'' with
         | Some (Tptr (Tprod t1 _)) =>
           Some (Ebinop oplus e'' (Evalue (Vint8 (Byte.repr (sizeof t1)))))
         | _ => None
       end)
    | Ecall f es => Some $ Ecall f es
    | Eassign e1 e2 => e'' ← resolve_lhs ev e1; Some (Eassign e'' e2)
    | Eif ex s1 s2 =>
      match resolve_lhs ev s1, resolve_lhs ev s2 with
        | Some s1', Some s2' => Some (Eif ex s1' s2')
        | _, _ => None
      end
    | Ewhile c ex s => Ewhile c ex <$> resolve_lhs ev s
    | Eseq s1 s2 =>
      match resolve_lhs ev s1, resolve_lhs ev s2 with
        | Some s1', Some s2' => Some (Eseq s1' s2')
        | _, _ => None
      end
    | Erete e => Some (Erete e)
  end.

Fixpoint add_params_to_env (e: env) (params: list (ident * type)) ls : env :=
  match params, ls with
    | (x, t)::ps, l::ls' => add_params_to_env (Env (sset x (t, l) (lenv e)) (fenv e)) ps ls'
    | _, _ => e
  end.

Definition instantiate_f_body (ev: env) (s: expr) : option expr :=
  (resolve_rhs ev s ≫= resolve_lhs ev).

Definition is_jump (e: expr) :=
  match e with
    | Ecall _ _ => true
    | Erete _ => true
    | _ => false
  end.

Inductive estep : expr → state → expr → state → Prop :=
| ESbinop: ∀ lv rv op σ v',
             evalbop op lv rv = Some v' →
             estep (Ebinop op (Evalue lv) (Evalue rv)) σ
                   (Evalue v') σ
| ESderef_typed:
    ∀ σ l v t,
      typeof v t →
      readbytes l (encode_val v) (s_heap σ) →
      estep (Ederef_typed t (Evalue (Vptr l))) σ
            (Evalue v) σ
| ESfst:
    ∀ v1 v2 σ,
      estep (Efst (Evalue (Vpair v1 v2))) σ (Evalue v1) σ
| ESsnd:
    ∀ v1 v2 σ,
      estep (Esnd (Evalue (Vpair v1 v2))) σ (Evalue v2) σ
| ESalloc:
    ∀ t v σ b o,
      typeof v t →
      (∀ o', (s_heap σ) !! (b, o') = None) →
      estep (Ealloc t (Evalue v)) σ (Evalue (Vptr (b, o)))
            (alloc_heap (b, o) v σ)
| ESassign:
    ∀ l v σ,
      estep (Eassign (Evalue (Vptr l)) (Evalue v))
            σ (Evalue Vvoid)
            (State (storebytes l (encode_val v) (s_heap σ)) (s_text σ))
| ESseq: ∀ s v σ, estep (Eseq (Evalue v) s) σ s σ
.

Inductive jstep: state → expr → list exprctx → expr → list exprctx → Prop :=
| JSrete:
    ∀ σ v k ks,
      jstep σ (Erete (Evalue v)) (k::ks) (fill_expr (Evalue v) k) ks
| JScall:
    ∀ σ es ls retty params f_body f_body' f k ks,
      es = map (fun l => Evalue (Vptr l)) ls →
      s_text σ !! f = Some (Function retty params f_body) →
      instantiate_f_body (add_params_to_env (Env [] []) params ls) f_body = Some f_body' →
      jstep σ (fill_expr (Ecall f es) k) ks f_body' (k::ks).

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.
Bind Scope prim_scope with prim.
Delimit Scope prim_scope with prim.

Inductive cstep: expr → state → list exprctx → expr → state → list exprctx → Prop :=
| HSestep: ∀ e e' σ σ' ks, estep e σ e' σ' → cstep e σ ks e' σ' ks
| HSjstep: ∀ e e' σ ks ks', jstep σ e ks e' ks' → cstep e σ ks e' σ ks'
| HSbind:
    ∀ e e' σ σ' kes ks,
      is_jump e = false →
      cstep e σ ks e' σ' ks →
      cstep (fill_ectxs e kes) σ ks (fill_ectxs e' kes) σ' ks.

(* Proven from operational semantics *)
Lemma fill_step_inv σ σ' ks ks' e c' Kes:
  is_jump e = false →
  to_val e = None →
  cstep (fill_ectxs e Kes) σ ks c' σ' ks' →
  (∃ e', c' =  (fill_ectxs e' Kes) ∧ estep e σ e' σ' ∧ ks = ks').
Admitted.

Lemma cstep_not_jump e e' σ σ' ks ks':
  is_jump e = false → cstep e σ ks e' σ' ks' → ks = ks'.
Admitted.      

Definition reducible cur σ ks := ∃ cur' σ' ks', cstep cur σ ks cur' σ' ks'.

(* Proven from operational semantics *)
Lemma lift_reducible e Kes σ ks:
  reducible e σ ks → reducible (fill_ectxs e Kes) σ ks.
Admitted.

Lemma estep_not_jump e σ e' σ':
  estep e σ e' σ' → is_jump e = false ∧ is_jump e' = false.
Admitted.

(* Proven from operational semantics *)
Lemma reducible_not_val c σ ks: reducible c σ ks → to_val c = None.
Admitted.

Instance state_inhabited: Inhabited state := populate (State ∅ ∅).

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
