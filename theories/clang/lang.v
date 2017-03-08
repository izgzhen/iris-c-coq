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
| Ealloc (t: type) (e: expr).
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

Record function (def_t: Type) :=
  Function {
      f_retty: type;
      f_params: decls;
      f_def: def_t
    }.

Definition program (t: Type) := ident → option (function t).

(* Operational Semantics *)

Inductive exprctx :=
| EKid
| EKbinopr (op: bop) (re: expr)
| EKbinopl (op: bop) (lv: val)
| EKderef_typed (t: type)
| EKaddrof
| EKfst
| EKsnd
| EKcall (fid: ident) (vargs: list val) (args: list expr)
| EKalloc (t: type).
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

Record env {t: Type} :=
  Env {
      lenv: smap (type * addr);
      fenv: smap (function t)
    }.

Fixpoint type_infer {t: Type} (ev: env) (e: expr) : option type :=
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
    | Ecall f args => f_retty t <$> sget f (fenv ev)
    | Ealloc t _ => Some (Tptr t)
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
    | EKalloc t => Ealloc t e
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

Definition heap := gmap addr byteval.
Definition text := gmap ident (function stmts).

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
            (alloc_heap (b, o) v σ).

(* Offset is ignored *)
Inductive sstep : stmts → state → stmts → state → Prop :=
| SSassign:
    ∀ l v σ,
      sstep (Sassign (Evalue (Vptr l)) (Evalue v))
            σ
            Sskip
            (State (storebytes l (encode_val v) (s_heap σ)) (s_text σ))
| SSseq: ∀ s σ, sstep (Sseq Sskip s) σ s σ
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

Fixpoint s_to_ret_val (s: stmts) :=
  match s with
    | Sret => Some Vvoid
    | Srete (Evalue v) => Some v
    | Sseq s1 s2 => s_to_ret_val s1
    | _ => None
  end.

Definition to_ret_val (c: cureval) :=
  match c with
    | curs s => s_to_ret_val s
    | cure _ => None
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

Fixpoint resolve_rhs_e {t: Type} (ev: @env t) (e: expr) : option expr :=
  match e with
    | Evar x => (* closed-ness? *)
      (match sget x (lenv ev) with
         | Some (t, l) => Some $ Ederef_typed t (Evalue (Vptr l))
         | None => None
       end)
    | Ebinop op e1 e2 =>
      match resolve_rhs_e ev e1, resolve_rhs_e ev e2 with
        | Some e1', Some e2' => Some (Ebinop op e1' e2')
        | _, _ => None
      end
    | Ederef e =>
      match type_infer ev e, resolve_rhs_e ev e with
        | Some (Tptr t), Some e' => Some (Ederef_typed t e') 
        | _, _ => None
      end
    | Eaddrof e => Eaddrof <$> resolve_rhs_e ev e
    | Efst e => Efst <$> resolve_rhs_e ev e
    | Esnd e => Esnd <$> resolve_rhs_e ev e
    | Ecall f args => Ecall f <$> lift_list_option (map (resolve_rhs_e ev) args)
    | _ => Some e
  end.

Fixpoint resolve_rhs {t: Type} (ev: @env t) (s: stmts) : option stmts :=
  match s with
    | Sskip => Some Sskip
    | Sprim p => Some $ Sprim p
    | Sassign e1 e2 => Sassign e1 <$> resolve_rhs_e ev e2
    | Sif e s1 s2 =>
      match resolve_rhs_e ev e, resolve_rhs ev s1, resolve_rhs ev s2 with
        | Some e', Some s1', Some s2' => Some $ Sif e' s1' s2'
        | _, _, _ => None
      end
    | Swhile c e s =>
      match resolve_rhs_e ev c, resolve_rhs_e ev e, resolve_rhs ev s with
        | Some c', Some e', Some s' => Some $ Swhile c' e' s'
        | _, _, _ => None
      end
    | Srete e => Srete <$> resolve_rhs_e ev e
    | Sret => Some Sret
    | Sseq s1 s2 =>
      match resolve_rhs ev s1, resolve_rhs ev s2 with
        | Some s1', Some s2' => Some (Sseq s1' s2')
        | _, _ => None
      end
  end.

Fixpoint resolve_lhs_e {t: Type} (ev: @env t) (e: expr) : option expr :=
  match e with
    | Evar x =>
      (match sget x (lenv ev) with
         | Some (_, l) => Some (Evalue (Vptr l))
         | None => None
       end)
    | Ederef e' => resolve_rhs_e ev e'
    | Efst e' => resolve_lhs_e ev e'
    | Esnd e' =>
      (e'' ← resolve_lhs_e ev e';
       match type_infer ev e'' with
         | Some (Tptr (Tprod t1 _)) =>
           Some (Ebinop oplus e'' (Evalue (Vint8 (Byte.repr (sizeof t1)))))
         | _ => None
       end)
    | Evalue (Vptr l) => Some e
    | Ecall f es => Some $ Ecall f es
    | _ => None
  end.

Fixpoint resolve_lhs {t: Type} (e: @env t) (s: stmts) : option stmts :=
  match s with
    | Sassign e1 e2 => e'' ← resolve_lhs_e e e1; Some (Sassign e'' e2)
    | Sif ex s1 s2 =>
      match resolve_lhs e s1, resolve_lhs e s2 with
        | Some s1', Some s2' => Some (Sif ex s1' s2')
        | _, _ => None
      end
    | Swhile c ex s => Swhile c ex <$> resolve_lhs e s
    | Sseq s1 s2 =>
      match resolve_lhs e s1, resolve_lhs e s2 with
        | Some s1', Some s2' => Some (Sseq s1' s2')
        | _, _ => None
      end
    | Sret => Some Sret
    | Srete e => Some (Srete e)
    | Sprim p => Some $ Sprim p
    | Sskip => Some Sskip
  end.

Fixpoint add_params_to_env {t: Type} (e: @env t) (params: list (ident * type)) ls : env :=
  match params, ls with
    | (x, t)::ps, l::ls' => add_params_to_env (Env _ (sset x (t, l) (lenv e)) (fenv e)) ps ls'
    | _, _ => e
  end.

Definition instantiate_f_body {t: Type} (ev: @env t) (s: stmts) : option stmts :=
  (resolve_rhs ev s ≫= resolve_lhs ev).

Inductive cstep: cureval → state → list context → cureval → state → list context → Prop :=
| CSestep: ∀ e e' σ σ' ks, estep e σ e' σ' → cstep (cure e) σ ks (cure e') σ' ks
| CSsstep: ∀ s s' σ σ' ks, sstep s σ s' σ' → cstep (curs s) σ ks (curs s') σ' ks
| CSecall:
    ∀ (ev: @env stmts) es vs ls retty params f_body f_body' f ks σ σ',
      es = map Evalue vs →
      params_match params vs →
      length ls = length vs →
      s_text σ !! f = Some (Function stmts retty params f_body) →
      instantiate_f_body (add_params_to_env ev params ls) f_body = Some f_body' →
      σ' = foldr (fun lv σ => alloc_heap (lv.1) (lv.2) σ) σ (zip ls vs) →
      cstep (cure (Ecall f es)) σ ks (curs f_body') σ' ks.

Lemma fill_step_inv σ σ' ks ks' e c' Kes Ks:
  to_val (cure e) = None →
  to_ret_val (cure e) = None →
  cstep (curs (fill_stmts (fill_ectxs e Kes) Ks)) σ ks c' σ' ks' →
  (∃ e', c' = curs (fill_stmts (fill_ectxs e' Kes) Ks) ∧ estep e σ e' σ' ∧ ks = ks').
Admitted.

Definition reducible cur σ ks := ∃ cur' σ' ks', cstep cur σ ks cur' σ' ks'.

Lemma lift_reducible e Kes Ks σ ks:
  reducible (cure e) σ ks → reducible (curs (fill_stmts (fill_ectxs e Kes) Ks)) σ ks.
Admitted.

Lemma reducible_not_val c σ ks: reducible c σ ks → to_val c = None.
Admitted.

Lemma reducible_not_ret_val c σ ks: reducible c σ ks → to_ret_val c = None.
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

Lemma fill_seq_inv s1 s2 ks1 ks2 σ1 σ2 e2:
  to_val (curs s1) = None →
  to_ret_val (curs s1) = None →
  cstep (curs (Sseq s1 s2)) σ1 ks1 e2 σ2 ks2 →
  (∃ s1',
     cstep (curs s1) σ1 ks1 (curs s1') σ2 ks2 ∧ e2 = curs (Sseq s1' s2) ∧ ks1 = ks2).
Admitted.
