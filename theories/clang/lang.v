(** Language definition **)

From iris.base_logic Require Export gen_heap big_op.
From iris.algebra Require Import gmap.
From iris_c.lib Require Export smap prelude.
From iris.program_logic Require Export language.
From iris_c.clang Require Export memory types.

Open Scope Z_scope.

(* Syntax *)

Inductive bop :=
| oplus
| ominus
| oequals
| oneq
| omult
| oless.

Definition decls := list (ident * type).

Definition tid := nat.

Inductive expr :=
| Evalue (v: val)
| Evar (x: ident)
| Elet_typed (t: type) (x: ident) (ex ebody: expr)
| ECAS_typed (t: type) (e1 e2 e3: expr)
| Ebinop (op: bop) (e1: expr) (e2: expr)
| Ederef (e: expr)
| Ederef_typed (t: type) (e: expr)
| Eaddrof (e: expr)
| Efst (e: expr)
| Esnd (e: expr)
| Ecall_typed (t: type) (fid: ident) (args: list expr)
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
| EKlet (t: type) (x: ident) (ebody: expr)
| EKbinopr (op: bop) (re: expr)
| EKbinopl (op: bop) (lv: val)
| EKCASl (t: type) (e1 e2: expr)
| EKCASm (t: type) (l0: addr) (e2: expr)
| EKCASr (t: type) (l0: addr) (v1: val)
| EKderef_typed (t: type)
| EKaddrof
| EKfst
| EKsnd
| EKcall (t: type) (fid: ident) (vargs: list val) (args: list expr)
| EKalloc (t: type)
| EKassignr (rhs: expr)
| EKassignl (lhs: addr)
| EKif (s1 s2: expr)
| EKwhile (cond: expr) (s: expr)
| EKrete
| EKseq (s: expr).

Definition env := smap type.

Fixpoint type_infer (ev: env) (e: expr) : option type :=
  match e with
    | Evalue v => Some (type_infer_v v)
    | Evar x => sget x ev
    | Ebinop _ e1 _ => type_infer ev e1 (* FIXME *)
    | ECAS_typed t _ e1 _ => Some t
    | Elet_typed t x ex ebody => type_infer (sset x t ev) ebody
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
    | Ecall_typed t f args => Some t
    | Ealloc t _ => Some (Tptr t)
    | _ => Some Tvoid
  end.

Definition fill_expr (e : expr) (Ke : exprctx) : expr :=
  match Ke with
    | EKbinopr op re => Ebinop op e re
    | EKbinopl op lv => Ebinop op (Evalue lv) e
    | EKCASl t e1 e2 => ECAS_typed t e e1 e2
    | EKCASm t l0 e2 => ECAS_typed t (Evalue (Vptr l0)) e e2
    | EKCASr t l0 v1 => ECAS_typed t (Evalue (Vptr l0)) (Evalue v1) e
    | EKderef_typed t => Ederef_typed t e
    | EKaddrof => Eaddrof e
    | EKfst => Efst e
    | EKsnd => Esnd e
    | EKcall t f vargs args => Ecall_typed t f (map Evalue vargs ++ e :: args)
    | EKalloc t => Ealloc t e
    | EKassignr rhs => Eassign e rhs
    | EKassignl lhs => Eassign (Evalue (Vptr lhs)) e
    | EKif s1 s2 => Eif e s1 s2
    | EKwhile c s => Ewhile c e s
    | EKrete => Erete e
    | EKseq s => Eseq e s
    | EKlet t x ebody => Elet_typed t x e ebody
  end.

Definition fill_ectxs := foldr (λ x y, fill_expr y x).
Definition heap := gmap addr byteval.
Definition text := gmap ident function.
Definition cont := list exprctx.
Definition stack := list cont.

Record state :=
  State {
      s_heap : heap;
      s_text : text;
      s_stack : stack
    }.

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
    | omult => (match v1, v2 with
                  | Vint8 i1, Vint8 i2 => Some (Vint8 (Byte.mul i1 i2))
                  | Vint32 i1, Vint32 i2 => Some (Vint32 (Int.mul i1 i2))
                  | _, _ => None
                 end)
    | oequals => if decide (v1 = v2) then Some vtrue else Some vfalse
    | oneq => if decide (v1 = v2) then Some vfalse else Some vtrue
    | oless => (match v1, v2 with
                  | Vint8 i1, Vint8 i2 => Some (b_to_v (Byte.lt i1 i2))
                  | Vint32 i1, Vint32 i2 => Some (b_to_v (Int.lt i1 i2))
                  | _, _ => None
                end)
  end.

Fixpoint readbytes l bs (σ: heap) :=
  match bs with
  | byte::bs' =>
    let '(b, o) := l in
    σ !! l = Some byte ∧ readbytes (b, o + 1)%nat bs' σ
  | _ => True
  end.

Lemma readbytes_segment σ bs': ∀ bs l,
  readbytes l (bs ++ bs') σ → readbytes l bs σ.
Proof.
  induction bs=>//.
  intros. destruct l. simpl in *.
  destruct H. split=>//.
  by apply IHbs.
Qed.

Lemma readbytes_segment_2 σ bs': ∀ bs l,
  readbytes l (bs ++ bs') σ → readbytes (shift_loc l (length bs)) bs' σ.
Proof.
  induction bs.
  - intros. destruct l. unfold shift_loc. simpl.
    replace ([] ++ bs') with bs' in H=>//.
    replace (n + 0)%nat with n=>//.
  - intros. destruct l. simpl in *.
    destruct H.
    specialize (IHbs _ H0).
    simpl in IHbs.
    replace (n + S (length bs))%nat with (n + 1 + length bs)%nat=>//.
    omega.
Qed.

Fixpoint storebytes l bs (σ: heap) :=
  match bs with
  | byte::bs' =>
    let '(b, o) := l in
    <[ l := byte ]> (storebytes (b, o + 1)%nat bs' σ)
  | _ => σ
  end.

Definition alloc_heap (l: addr) (v: val) (σ: heap) : heap :=
  storebytes l (encode_val v) σ.

Definition to_val (c: expr) :=
  match c with
    | Evalue v => Some v
    | _ => None
  end.

Lemma to_of_val v: to_val (Evalue v) = Some v.
Proof. done. Qed.

Lemma of_to_val e v : to_val e = Some v → Evalue v = e.
Proof. induction e; crush. Qed.

Lemma fill_ectx_not_val e K: to_val (fill_expr e K) = None.
Proof. induction K; crush. Qed.

Lemma fill_ectxs_not_val Kes:
  ∀ e, to_val e = None → to_val (fill_ectxs e Kes) = None.
Proof. induction Kes; first by inversion 1.
       intros. simpl. apply fill_ectx_not_val.
Qed.

Fixpoint resolve_rhs (ev: env) (x: ident) (vx: val) (tx: type) (e: expr) : option expr :=
  match e with
    | Evalue v => Some e
    | Ederef_typed t e => Ederef_typed t <$> resolve_rhs ev x vx tx e
    | Ealloc t e => Ealloc t <$> resolve_rhs ev x vx tx e
    | Evar x' => (* closed-ness? *)
      (if bool_decide (x' = x)
         then Some $ Ederef_typed tx (Evalue vx)
         else Some e)
    | Ebinop op e1 e2 =>
      match resolve_rhs ev x vx tx e1, resolve_rhs ev x vx tx e2 with
        | Some e1', Some e2' => Some (Ebinop op e1' e2')
        | _, _ => None
      end
    | Ederef e =>
      match type_infer ev e, resolve_rhs ev x vx tx e with
        | Some (Tptr t), Some e' => Some (Ederef_typed t e')
        | _, _ => None
      end
    | Eaddrof e => Eaddrof <$> resolve_rhs ev x vx tx e
    | Efst e => Efst <$> resolve_rhs ev x vx tx e
    | Esnd e => Esnd <$> resolve_rhs ev x vx tx e
    | Ecall_typed t f args => Ecall_typed t f <$> lift_list_option (map (resolve_rhs ev x vx tx) args)
    | Eassign e1 e2 => Eassign e1 <$> resolve_rhs ev x vx tx e2
    | Eif e s1 s2 =>
      match resolve_rhs ev x vx tx e, resolve_rhs ev x vx tx s1, resolve_rhs ev x vx tx s2 with
        | Some e', Some s1', Some s2' => Some $ Eif e' s1' s2'
        | _, _, _ => None
      end
    | Ewhile c e s =>
      match resolve_rhs ev x vx tx c, resolve_rhs ev x vx tx e, resolve_rhs ev x vx tx s with
        | Some c', Some e', Some s' => Some $ Ewhile c' e' s'
        | _, _, _ => None
      end
    | Erete e => Erete <$> resolve_rhs ev x vx tx e
    | Eseq s1 s2 =>
      match resolve_rhs ev x vx tx s1, resolve_rhs ev x vx tx s2 with
        | Some s1', Some s2' => Some (Eseq s1' s2')
        | _, _ => None
      end
    | ECAS_typed t e1 e2 e3 =>
      match resolve_rhs ev x vx tx e1, resolve_rhs ev x vx tx e2, resolve_rhs ev x vx tx e3 with
        | Some e1', Some e2', Some e3' => Some (ECAS_typed t e1' e2' e3')
        | _, _, _ => None
      end
    | Elet_typed t y ey ebody =>
      if bool_decide (x = y)
      then Some e
      else match resolve_rhs ev x vx tx ey with
             | Some ey' => Elet_typed t y ey' <$> (resolve_rhs (sset y t ev) x vx tx ebody)
             | _ => None
           end
  end.

Fixpoint resolve_lhs_inner (ev: env) (x: ident) (vx: val) (tx: type) (e: expr) : option expr :=
  match e with
    | Evalue (Vptr l) => Some e
    | Ederef_typed _ e' => Some e
    | Evar x' =>
      if bool_decide (x = x')
      then Some (Evalue vx)
      else Some e
    | Ederef e' => resolve_rhs ev x vx tx e'
    | Efst e' => resolve_lhs_outer ev x vx tx e'
    | Esnd e' =>
      (e'' ← resolve_lhs_inner ev x vx tx e';
       match type_infer ev e'' with
         | Some (Tptr (Tprod t1 _)) =>
           Some (Ebinop oplus e'' (Evalue (Vint8 $ Byte.repr (sizeof t1))))
         | _ => None
       end)
    | Ebinop op e1 e2 =>
      match resolve_lhs_inner ev x vx tx e1, resolve_rhs ev x vx tx e2 with
        | Some e1, Some e2 => Some $ Ebinop op e1 e2
        | _, _ => None
      end
    | _ => None
  end
with
resolve_lhs_outer (ev: env) (x: ident) (vx: val) (tx: type) (e: expr) : option expr :=
  match e with
    | Eassign e1 e2 => e'' ← resolve_lhs_inner ev x vx tx e1; Some (Eassign e'' e2)
    | Eif ex s1 s2 =>
      match resolve_lhs_outer ev x vx tx s1, resolve_lhs_outer ev x vx tx s2 with
      | Some s1', Some s2' => Some (Eif ex s1' s2')
      | _, _ => None
      end
    | Ewhile c ex s => Ewhile c ex <$> resolve_lhs_outer ev x vx tx s
    | Eseq s1 s2 =>
      match resolve_lhs_outer ev x vx tx s1, resolve_lhs_outer ev x vx tx s2 with
        | Some s1', Some s2' => Some (Eseq s1' s2')
        | _, _ => None
      end
    | Elet_typed t y ey ebody =>
      if bool_decide (x = y)
      then Some e
      else Elet_typed t y ey <$> (resolve_lhs_outer (sset y t ev) x vx tx ebody)
    | _ => Some e
  end.

Definition instantiate_let (x: ident) (vx: val) (tx: type) (s: expr) : option expr :=
  (resolve_rhs (ssig x tx) x vx tx s ≫= resolve_lhs_outer (ssig x tx) x vx tx).

Fixpoint is_jmp (e: expr) :=
  match e with
    | Ecall_typed _ _ es => true
    | Erete e => true
    | Ebinop _ e1 e2 => is_jmp e1 || is_jmp e2
    | Ederef e => is_jmp e
    | Ederef_typed _ e => is_jmp e
    | Eaddrof e => is_jmp e
    | Efst e => is_jmp e
    | Esnd e => is_jmp e
    | Ealloc _ e => is_jmp e
    | Eassign e1 e2 => is_jmp e1 || is_jmp e2
    | Eif e1 e2 e3 => is_jmp e1 || is_jmp e2 || is_jmp e3
    | Eseq e1 e2 => is_jmp e1 || is_jmp e2
    | Ewhile c e e2 => is_jmp e || is_jmp c || is_jmp e2
    | ECAS_typed t e1 e2 e3 => is_jmp e1 || is_jmp e2 || is_jmp e3
    | Elet_typed t x ex ebody => is_jmp ex || is_jmp ebody
    | _ => false
  end.

Inductive jnf: expr → Prop :=
  | JNFcall: ∀ t f vs, jnf (Ecall_typed t f (map Evalue vs))
  | JNFrete: ∀ v, jnf (Erete (Evalue v)).

Global Hint Constructors jnf.

Ltac solve_is_jmp_false :=
  repeat (
      match goal with
      | [ H: is_jmp _ = false |- _ ] => rewrite H
      end);
  repeat (
      match goal with
      | [ H : context [ is_jmp ?E ] |- _ ] => destruct (is_jmp E)
      end);
  auto.

Lemma is_jmp_rec' e K:
  is_jmp (fill_expr e K) = false → is_jmp e = false.
Proof. induction K=>//; simpl; intros; solve_is_jmp_false. Qed.

Lemma is_jmp_rec e ks:
  is_jmp (fill_ectxs e ks) = false → is_jmp e = false.
Proof. induction ks=>//. simpl; intros. apply is_jmp_rec' in H. auto. Qed.

Lemma is_jmp_out' e e' K:
  is_jmp e' = false →
  is_jmp (fill_expr e K) = false →
  is_jmp (fill_expr e' K) = false.
Proof. induction K=>//; simpl; intros; solve_is_jmp_false. Qed.

Lemma is_jmp_out e e' K:
  is_jmp e' = false →
  is_jmp (fill_ectxs e K) = false →
  is_jmp (fill_ectxs e' K) = false.
Proof.
  induction K=>//. simpl. intros. eapply is_jmp_out'=>//.
  apply IHK=>//. eapply is_jmp_rec'=>//.
Qed.

Inductive estep : expr → heap → expr → heap → Prop :=
| ESbinop: ∀ lv rv op σ v',
             evalbop op lv rv = Some v' →
             estep (Ebinop op (Evalue lv) (Evalue rv)) σ
                   (Evalue v') σ
| ESderef_typed:
    ∀ σ l v t,
      typeof v t →
      readbytes l (encode_val v) σ →
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
      (∀ o', σ !! (b, o') = None) →
      estep (Ealloc t (Evalue v)) σ (Evalue (Vptr (b, o)))
            (alloc_heap (b, o) v σ)
| ESassign:
    ∀ l v σ,
      estep (Eassign (Evalue (Vptr l)) (Evalue v))
            σ (Evalue Vvoid)
            (storebytes l (encode_val v) σ)
| ESseq: ∀ s v σ, estep (Eseq (Evalue v) s) σ s σ
| ESwhile_true:
    ∀ s cond σ,
      estep (Ewhile cond (Evalue vtrue) s) σ (Eseq s (Ewhile cond cond s)) σ
| ESwhile_false:
    ∀ s cond σ,
      estep (Ewhile cond (Evalue vfalse) s) σ (Evalue Vvoid) σ
| ESCASFail l t v1 v2 vl σ :
    typeof v1 t →
    typeof v2 t →
    typeof vl t →
    readbytes l (encode_val vl) σ → vl ≠ v1 →
    estep (ECAS_typed t (Evalue (Vptr l)) (Evalue v1) (Evalue v2)) σ
          (Evalue vfalse) σ
| ESCASSuc l t v1 v2 σ :
    typeof v1 t →
    typeof v2 t →
    readbytes l (encode_val v1) σ →
    estep (ECAS_typed t (Evalue (Vptr l)) (Evalue v1) (Evalue v2)) σ
          (Evalue vtrue) (storebytes l (encode_val v2) σ)
| ESlet t x xv e e' σ:
    instantiate_let x xv t e = Some e' →
    estep (Elet_typed t x (Evalue xv) e) σ e' σ
| ESifTrue e1 e2 σ:
    estep (Eif (Evalue vtrue) e1 e2) σ e1 σ
| ESifFalse e1 e2 σ:
    estep (Eif (Evalue vfalse) e1 e2) σ e2 σ
| ESbind':
    ∀ e e' σ σ' k kes,
      is_jmp e = false →
      estep e σ e' σ' →
      estep (fill_ectxs e (k::kes)) σ (fill_ectxs e' (k::kes)) σ'.
(* !!!!!!!!!!!: NEVER add new semantic rules after ESbind', which would break everything *)

Lemma ESbind:
    ∀ kes e e' σ σ',
      is_jmp e = false →
      estep e σ e' σ' →
      estep (fill_ectxs e kes) σ (fill_ectxs e' kes) σ'.
Proof. induction kes=>//. intros. apply ESbind'=>//. Qed.

Lemma estep_not_val {e σ e' σ'}:
  estep e σ e' σ' → to_val e = None.
Proof. induction 1=>//. by apply fill_ectxs_not_val. Qed.

Definition is_val e := is_some (to_val e).

Lemma to_val_is_val e:
  to_val e = None ↔ is_val e = false.
Proof. induction e; crush. Qed.

Lemma forall_is_val vs:
  forallb is_val (map Evalue vs) = true.
Proof. by induction vs=>//. Qed.

Definition is_loc e :=
  match to_val e with
    | Some (Vptr _) => true
    | _ => false
  end.

Fixpoint unfill_expr (e: expr) (ks: cont) : option (cont * expr) :=
  match e with
    | Evalue _ => None
    | Evar _ => None
    | Ebinop op e1 e2 =>
      match e1, e2 with
        | Evalue v1, Evalue v2 => Some (ks, e)
        | Evalue v1, _ => unfill_expr e2 (EKbinopl op v1 :: ks)
        | _, _ => unfill_expr e1 (EKbinopr op e2 :: ks)
      end
    | Ederef_typed t e =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKderef_typed t :: ks)
      end
    | Eaddrof e =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKaddrof :: ks)
      end
    | Efst e =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKfst :: ks)
      end
    | Esnd e =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKsnd :: ks)
      end
    (* | Ecall : ident → list expr → expr *) (* which is complex ... *)
    | Ealloc t e =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKalloc t :: ks)
      end
    | Eassign e1 e2 =>
      match e1, e2 with
        | Evalue v1, Evalue v2 => Some (ks, e)
        | Evalue (Vptr l), _ => unfill_expr e2 (EKassignl l :: ks)
        | _, _ => unfill_expr e1 (EKassignr e2 :: ks)
      end
    | Eif e1 e2 e3 =>
      match e1 with
        | Evalue _ => Some (ks, e)
        | _ => unfill_expr e1 (EKif e2 e3 :: ks)
      end
    | Ewhile c e1 s =>
      match e1 with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e1 (EKwhile c s :: ks)
      end
    | Erete e1 =>
      match e1 with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e1 (EKrete :: ks)
      end
    | Eseq e1 e2 =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e1 (EKseq e2 :: ks)
      end
    | Ecall_typed t f es =>
      if forallb is_val es
        then Some (ks, e)
        else None (* Unsound *)
    | ECAS_typed t e1 e2 e3 =>
      match e1, e2, e3 with
      | Evalue (Vptr l), Evalue v2, Evalue v3 => Some (ks, e)
      | Evalue (Vptr l), Evalue v2, _ => unfill_expr e3 (EKCASr t l v2 :: ks)
      | Evalue (Vptr l), _, _ => unfill_expr e2 (EKCASm t l e3 :: ks)
      | _, _, _ => unfill_expr e1 (EKCASl t e2 e3 :: ks)
      end
    | Elet_typed t x ex ebody =>
      match ex with
        | Evalue _ => Some (ks, e)
        | _ => unfill_expr ex (EKlet t x ebody :: ks)
      end
    | _ => None
  end.

Inductive lnf: expr → Prop :=
  | LNFbinop: ∀ op v1 v2, lnf (Ebinop op (Evalue v1) (Evalue v2))
  | LNFderef: ∀ v, lnf (Ederef (Evalue v))
  | LNFderef_typed: ∀ t v, lnf (Ederef_typed t (Evalue v))
  | LNFaddrof: ∀ v, lnf (Eaddrof (Evalue v))
  | LNFfst: ∀ v, lnf (Efst (Evalue v))
  | LNFsnd: ∀ v, lnf (Esnd (Evalue v))
  | LNFalloc: ∀ t v, lnf (Ealloc t (Evalue v))
  | LNFassign: ∀ l v, lnf (Eassign (Evalue (Vptr l)) (Evalue v))
  | LNFif: ∀ v e2 e3, lnf (Eif (Evalue v) e2 e3)
  | LNFseq: ∀ v e2, lnf (Eseq (Evalue v) e2)
  | LNFwhile: ∀ c v s, lnf (Ewhile c (Evalue v) s)
  | LNFCAS: ∀ l t v1 v2, lnf (ECAS_typed t (Evalue (Vptr l)) (Evalue v1) (Evalue v2))
  | LNFlet: ∀ t x v e2, lnf (Elet_typed t x (Evalue v) e2).

Inductive enf: expr → Prop :=
| jnf_enf: ∀ e, jnf e → enf e
| lnf_enf: ∀ e, lnf e → enf e.

Global Hint Constructors lnf enf.

Lemma enf_not_val e: enf e → to_val e = None.
Proof. induction e; crush. inversion H; inversion H0. Qed.

Lemma fill_app e K K': fill_ectxs (fill_ectxs e K) K' = fill_ectxs e (K' ++ K).
Proof. induction K'=>//. simpl. by rewrite IHK'. Qed.

Definition unfill e kes := unfill_expr (fill_ectxs e kes) [] = Some (kes, e).

Axiom cont_uninj: ∀ kes e, enf e → unfill e kes.

Axiom cont_uninj':
  ∀ e eh K, unfill_expr e [] = Some (K, eh) → enf eh ∧ e = fill_ectxs eh K.

Arguments cont_uninj' {_ _ _} _.

Lemma unfill_app e eh K K':
  unfill_expr e [] = Some (K, eh) →
  unfill_expr (fill_ectxs e K') [] = Some (K' ++ K, eh).
Proof.
  intros H. move: (cont_uninj' H) => [? ?].
  subst. rewrite fill_app. by apply cont_uninj.
Qed.

Lemma cont_inj {e e' kes kes'}:
  enf e → enf e' →
  fill_ectxs e kes = fill_ectxs e' kes' → e = e' ∧ kes = kes'.
Proof.
  intros H H' Heq. apply (cont_uninj kes) in H.
  apply (cont_uninj kes') in H'.
  unfold unfill in H', H.
  rewrite Heq in H. by simplify_eq.
Qed.

Lemma fill_not_enf e k:
  is_val e = false → enf (fill_expr e k) → False.
Proof. induction k=>//; simpl; intros H1 H2;
       try (inversion H2; by subst);
       try (inversion H2;
            [ inversion H | subst; inversion H; by subst ]).
       - assert (forallb is_val (map Evalue vargs ++ e :: args) = true) as Hcontra.
         { subst. rewrite -H6. apply forall_is_val. }
         rewrite forallb_app in Hcontra.
         replace (e::args) with ([e] ++ args) in Hcontra; last done.
         rewrite forallb_app in Hcontra. simpl in Hcontra. rewrite H1 in Hcontra.
           by rewrite andb_false_r in Hcontra.
       - subst. done.
Qed.

Lemma escape_false {e a e' a2 kes k0 e''}:
  estep e a e' a2 →
  fill_expr (fill_ectxs e kes) k0 = e'' → enf e'' → False.
Proof.
  intros. subst. eapply fill_not_enf=>//.
  apply to_val_is_val, fill_ectxs_not_val. by eapply estep_not_val.
Qed.

Lemma escape_false' {e a e' a2 kes k0}:
  estep e a e' a2 →
  enf (fill_expr (fill_ectxs e kes) k0) → False.
Proof. intros Hes Henf. eapply escape_false=>//. Qed.

Ltac gen_eq H E1 E2 KS :=
  replace E1 with (fill_ectxs E1 []) in H; last done;
  assert (E1 = E2 ∧ [] = KS) as [? ?];
  [ apply cont_inj=>// | subst; clear H ].

Lemma fill_cons e K K': fill_expr (fill_ectxs e K) K' = fill_ectxs e (K' :: K).
Proof. induction K'=>//. Qed.

Axiom cont_ind:
  ∀ P: cont → Prop,
    (P []) →
    (∀ ks, (∀ ks', length ks' < length ks → P ks')%nat → P ks) →
    (∀ ks, P ks).

Axiom unfill_segment: ∀ e ks eh ks',
  to_val e = None → enf eh →
  fill_ectxs e ks = fill_ectxs eh ks' →
  ∃ ks'', ks' = ks ++ ks'' ∧ e = fill_ectxs eh ks''.

Arguments unfill_segment {_ _ _ _} _ _ _.

Ltac inversion_cstep Hnf tac :=
  match goal with
      | [ H : estep (fill_ectxs _ _) _ _ _ |- _ ] => (
          inversion H=>//;
          try (match goal with
               | [ H2 : fill_expr (fill_ectxs ?E _) _ =
                        fill_ectxs ?E2 ?KS |- _ ] =>
                 rewrite fill_cons in H2; subst;
                 match goal with
                 | [ H3 : estep E _ _ _ |- _ ] =>
                   let Hnv := fresh "Hnv" in
                   move: (estep_not_val H3) => Hnv;
                   destruct (unfill_segment Hnv Hnf H2) as [K' [? ?]]; subst
                 end
               | _ => subst; match goal with
                             | [ H : ?E1 = fill_ectxs ?E2 ?KS |- _ ] =>
                                 by (gen_eq H E1 E2 KS; eauto; tac)
                             end
               end)
        )
    end.

Lemma focus_estep_inv' eh1 σ1 σ2:
  enf eh1 →
  let P K :=
      (∀ e2,
         estep (fill_ectxs eh1 K) σ1 e2 σ2 →
         ∃ eh2, estep eh1 σ1 eh2 σ2 ∧ e2 = fill_ectxs eh2 K
      )
  in ∀ K, P K.
Proof.
  intros Hnf P. apply (cont_ind P).
  - unfold P. eauto.
  - unfold P. intros ks Hind e2 Hes.
    inversion_cstep Hnf idtac.
    apply (Hind K') in H1.
    + destruct H1 as [eh2 [? ?]].
      subst. exists eh2.  split=>//. by rewrite fill_app.
    + rewrite app_length. simpl. omega.
Qed.

Lemma focus_estep_inv'' {eh1 σ1 σ2}:
  enf eh1 →
  ∀ K e2,
    estep (fill_ectxs eh1 K) σ1 e2 σ2 →
    ∃ eh2, estep eh1 σ1 eh2 σ2 ∧ e2 = fill_ectxs eh2 K.
Proof. intros H. move: (focus_estep_inv' eh1 σ1 σ2 H) => /= H'. done. Qed.

Axiom focus_estep: ∀ e1 σ1 e2 σ2,
  estep e1 σ1 e2 σ2 → ∃ K eh1, e1 = fill_ectxs eh1 K ∧ enf eh1.

Arguments focus_estep {_ _ _ _} _.

Lemma focus_estep_inv {e1 σ1 e2 σ2}:
  estep e1 σ1 e2 σ2 →
  ∃ e1' e2' K, enf e1' ∧ e1 = fill_ectxs e1' K ∧ estep e1' σ1 e2' σ2 ∧ e2 = fill_ectxs e2' K.
Proof.
  intros H. move: (focus_estep H) => [K [eh1 [? H']]].
  subst. exists eh1.
  destruct (@focus_estep_inv'' eh1 σ1 σ2 H' K e2) as [e' [? ?]]=>//.
  eexists _, _. split=>//; split=>//.
Qed.

Tactic Notation "escape_false" :=
  exfalso;
  match goal with
  | [ Hes: estep ?e ?a ?e' ?a2,
      Heq: fill_expr (fill_ectxs ?e ?kes) ?k0 = ?e'' |- _ ] =>
      by eapply (escape_false Hes Heq)=>//; auto
  | [ Hes: estep ?e ?a ?e' ?a2,
      Henf: enf (fill_expr (fill_ectxs ?e ?kes) ?k) |- _ ] =>
      by eapply (escape_false' Hes Henf)=>//; auto
  end.

Lemma estep_call_false t f vs σ1 e' σ2:
  estep (Ecall_typed t f (map Evalue vs)) σ1 e' σ2 → False.
Proof. inversion 1. subst. escape_false. Qed.

Lemma estep_ret_false v σ1 e' σ2:
  estep (Erete (Evalue v)) σ1 e' σ2 → False.
Proof. inversion 1. subst. escape_false. Qed.

Lemma fill_estep_false' e σ σ':
  jnf e →
  let P K :=
      (∀ e', estep (fill_ectxs e K) σ e' σ' → False)
  in ∀ K, P K.
Proof.
  intros Hjn P. assert (enf e) as Henf; first by apply jnf_enf.
  apply (cont_ind P).
  - unfold P. simpl. intros.
    inversion Hjn; subst.
    + by eapply estep_call_false.
    + by eapply estep_ret_false.
  - unfold P. intros ks Hind e' Hes.
    inversion_cstep Henf ltac:(inversion Hjn).
    apply (Hind K') in H1=>//.
    rewrite app_length. simpl. omega.
Qed.

Lemma fill_estep_false {e kes e' σ σ'}:
  jnf e →
  estep (fill_ectxs e kes) σ e' σ' → False.
Proof. intros H. move: (fill_estep_false' e σ σ' H kes e') => /= H'. done. Qed.

Axiom not_val_ind:
  ∀ P: expr → Prop,
    (∀ e, enf e → P e) →
    (∀ e ks, to_val e = None → P e → P (fill_ectxs e ks)) →
    (∀ e, to_val e = None → P e).

Axiom not_val_ind':
  ∀ P: expr → Prop,
    (∀ e, enf e → P e) →
    (∀ e ks, enf e →
             (∀ ks', length ks' < length ks →
                     P (fill_ectxs e ks'))%nat → P (fill_ectxs e ks)) →
    (∀ e, to_val e = None → P e).

Lemma fill_estep_inv':
  let P e :=
    (∀ e' σ σ' ks,
       is_jmp e = false →
       estep (fill_ectxs e ks) σ e' σ' →
       ∃ e'', estep e σ e'' σ' ∧ e' = fill_ectxs e'' ks)
  in ∀ e, to_val e = None → P e.
Proof.
  intros P. apply (not_val_ind P).
  - unfold P. intros e Henf e' σ σ' ks Hnj Hes.
    eapply focus_estep_inv in Hes.
    destruct Hes as (e1'&e2'&K&Henf'&Heq&Hes'&Heq'). subst.
    eapply cont_inj in Heq=>//.
    destruct Heq. subst. eauto.
  - unfold P. intros e ks Hnv Hind e' σ σ' ks' Hnj Hes.
    rewrite fill_app in Hes.
    apply Hind in Hes; last by eapply is_jmp_rec.
    destruct Hes as (e''&Hes''&Heq').
    exists (fill_ectxs e'' ks).
    split.
    { apply ESbind=>//. by eapply is_jmp_rec. }
    { by rewrite fill_app. }
Qed.

Lemma fill_estep_inv {e ks a a1 a2}:
  to_val e = None →
  is_jmp e = false →
  estep (fill_ectxs e ks) a a1 a2 →
  ∃ e', estep e a e' a2 ∧ a1 = fill_ectxs e' ks.
Proof. move: fill_estep_inv' => /= H. intros. apply H=>//. Qed.

Lemma cont_incl':
  let P e' :=
      (∀ e kes kes',
        enf e →
        fill_ectxs e kes = fill_ectxs e' kes' →
        ∃ kes'', e' = fill_ectxs e kes'')
  in ∀ e', to_val e' = None → P e'.
Proof.
  intros P. apply (not_val_ind P).
  - unfold P. intros e Henf e' kes kes' Henf' Heq.
    apply cont_inj in Heq=>//.
    destruct Heq. subst.
    by exists [].
  - unfold P. intros e ks Hnv Hind e' kes kes' Henf' Heq.
    rewrite fill_app in Heq.
    apply Hind in Heq=>//.
    destruct Heq. subst. rewrite fill_app. eauto.
Qed.

Lemma cont_incl {e' kes kes' e}:
  enf e →
  to_val e' = None →
  fill_ectxs e kes = fill_ectxs e' kes' →
  ∃ kes'', e' = fill_ectxs e kes''.
Proof. move: cont_incl' => /= H. intros. by eapply H. Qed.

Fixpoint let_params (vs: list val) (params: decls) e : option expr :=
  match vs, params with
    | v::vs', (x, tx)::ps' => Elet_typed tx x (Ealloc tx (Evalue v)) <$> let_params vs' ps' e
    | [], [] => Some e
    | _, _ => None
  end.

Inductive jstep: text → expr → stack → expr → stack → Prop :=
| JSrete:
    ∀ t v k k' ks,
      unfill (Erete (Evalue v)) k' →
      jstep t
            (fill_ectxs (Erete (Evalue v)) k') (k::ks)
            (fill_ectxs (Evalue v) k) ks
| JScall:
    ∀ vs e' retty params f_body f t k ks,
      t !! f = Some (Function retty params f_body) →
      let_params vs params f_body = Some e' →
      jstep t (fill_ectxs (Ecall_typed retty f (map Evalue vs)) k) ks
            e' (k::ks).

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.

Inductive cstep: expr → state → expr → state → Prop :=
| CSestep:
    ∀ s t e h e' h', estep e h e' h' → cstep e (State h t s) e' (State h' t s)
| CSjstep:
    ∀ e e' h t s s' , jstep t e s e' s' → cstep e (State h t s) e' (State h t s').

Ltac inversion_estep :=
  match goal with [ H : estep _ _ _ _ |- _ ] => inversion H end.

Ltac inversion_cstep_as Hes Hjs :=
  match goal with
    | [ Hcs : cstep _ _ _ _ |- _ ] =>
      inversion Hcs as [???????Hes|???????Hjs]; subst
  end.

Ltac inversion_jstep_as Heq :=
  match goal with
  | [ Hjs: jstep _ _ _ _ _ |- _ ] =>
    inversion Hjs as [?|?]; subst;
    match goal with
    | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _ ] => rename H into Heq
    | _ => idtac
    end
  end.

Global Hint Constructors estep jstep cstep.

Lemma is_jmp_ret k' v: is_jmp (fill_ectxs (Erete (Evalue v)) k') = true.
Proof. induction k'=>//. simpl; induction a; simpl; try (rewrite IHk'); auto. Qed.

Lemma is_jmp_call k' t f es: is_jmp (fill_ectxs (Ecall_typed t f es) k') = true.
Proof. induction k'=>//. simpl; induction a; simpl; try (rewrite IHk'); auto. Qed.

Lemma is_jmp_jstep_false {e e' σ} k {ks ks'}:
  to_val e = None →
  is_jmp e = false →
  jstep σ (fill_ectxs e k) ks e' ks' → false.
Proof.
  intros Hnv Hnj.
  inversion 1; subst;
    match goal with
    | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _ ] =>
      symmetry in H;
      apply unfill_segment in H=>//;
      destruct H as [? [? ?]]; subst
    end.
  - by rewrite is_jmp_ret in Hnj.
  - auto.
  - by rewrite is_jmp_call in Hnj.
  - auto.
Qed.

Lemma cstep_not_val {e σ e' σ'}:
  cstep e σ e' σ' → to_val e = None.
Proof.
  inversion 1; subst.
  - by eapply estep_not_val.
  - inversion_jstep_as Heq; by apply fill_ectxs_not_val.
Qed.

Lemma CSbind' e e' σ σ' k kes:
  is_jmp e = false →
  cstep e σ e' σ' →
  cstep (fill_ectxs e (k::kes)) σ (fill_ectxs e' (k::kes)) σ'.
Proof.
  intros Hnj Hcs. inversion Hcs; subst.
  - apply CSestep. apply ESbind=>//.
  - exfalso. move: (cstep_not_val Hcs) => Hn.
    apply (is_jmp_jstep_false [] Hn Hnj H).
Qed.

Lemma CSbind:
    ∀ e e' σ σ' kes,
      is_jmp e = false →
      cstep e σ e' σ' →
      cstep (fill_ectxs e kes) σ (fill_ectxs e' kes) σ'.
Proof. induction kes=>//. intros. apply CSbind'=>//. Qed.

Instance state_inhabited: Inhabited state := populate (State ∅ ∅ []).

Lemma not_jmp_preserves k e e' σ σ':
  to_val e = None →
  is_jmp e = false →
  cstep (fill_ectxs e k) σ e' σ' →
  s_stack σ = s_stack σ' ∧ s_text σ = s_text σ' ∧
  estep (fill_ectxs e k) (s_heap σ) e' (s_heap σ').
Proof.
  intros Hnv Hnj Hcs. inversion Hcs; subst=>//.
  exfalso. eapply (is_jmp_jstep_false k)=>//.
Qed.

Lemma fill_step_inv e1' σ1 e2 σ2 K:
  to_val e1' = None →
  is_jmp e1' = false →
  cstep (fill_ectxs e1' K) σ1 e2 σ2 →
  ∃ e2', e2 = fill_ectxs e2' K ∧ cstep e1' σ1 e2' σ2 ∧ s_stack σ1 = s_stack σ2.
Proof.
  intros Hnv Hnj.
  inversion 1; subst.
  - match goal with
    | [ H : estep _ _ _ _ |- _ ] =>
      eapply fill_estep_inv in H=>//;
      destruct H as (e2'&?&?)
    end; exists e2'; split; [| split ]; auto.
  - inversion_jstep_as Heq;
    eapply cont_incl in Heq=>//;
    destruct Heq as (?&?); subst.
    + by rewrite is_jmp_ret in Hnj.
    + auto.
    + by rewrite is_jmp_call in Hnj.
    + auto.
Qed.

Lemma instantiate_let_preserves_not_jmp x xv xt e e':
  instantiate_let x xv xt e = Some e' →
  is_jmp e = false →
  is_jmp e' = false.
Admitted. (* Apparent but hard for now. Documented *)

Lemma estep_preserves_not_jmp' σ1 σ2:
  let P e1 :=
      (∀ e2, is_jmp e1 = false → estep e1 σ1 e2 σ2 → is_jmp e2 = false)
  in ∀ e1, to_val e1 = None → P e1.
Proof.
  intros P. apply (not_val_ind' P).
  - unfold P. intros e Henf e2 Hjn Hes.
    inversion Hes=>//; subst; simpl in Hes=>//; simpl in Hjn.
    + inversion Hjn. simpl. solve_is_jmp_false.
    + by eapply instantiate_let_preserves_not_jmp.
    + solve_is_jmp_false.
    + solve_is_jmp_false.
    + simpl in Hjn. exfalso.
      simpl in Henf. escape_false.
  - unfold P. intros e ks Henf Hind e2 Hjn Hes.
    inversion_cstep Henf ltac:(inversion Hjn); simplify_eq
    ; try by (simpl; rewrite -H0 in Hjn; inversion Hjn; solve_is_jmp_false).
    + simplify_eq. eapply instantiate_let_preserves_not_jmp=>//.
      rewrite -H in Hjn. by simpl in Hjn.
    + assert (is_jmp e' = false).
      { apply (Hind K')=>//. rewrite app_length. simpl. omega. }
      rewrite -fill_app in Hjn.
      eapply is_jmp_out in Hjn=>//.
Qed.

Lemma estep_preserves_not_jmp'' e σ1 e2' σ2:
  to_val e = None → is_jmp e = false →
  estep e σ1 e2' σ2 → is_jmp e2' = false.
Proof.
  intros H. move: (estep_preserves_not_jmp' σ1 σ2 e H e2') => /= H'. done.
Qed.

Lemma estep_preserves_not_jmp e σ1 e2' σ2:
  is_jmp e = false → estep e σ1 e2' σ2 → is_jmp e2' = false.
Proof.
  destruct (to_val e) eqn:Heq.
  - apply of_to_val in Heq. subst. inversion 2.
    subst. exfalso. apply estep_not_val in H0=>//.
  - by apply estep_preserves_not_jmp''.
Qed.

Lemma cstep_preserves_not_jmp e σ1 e2' σ2:
  is_jmp e = false → cstep e σ1 e2' σ2 → is_jmp e2' = false.
Proof.
  inversion 2; subst.
  - inversion_estep; subst=>//; try by (simpl in *; solve_is_jmp_false).
    + by eapply instantiate_let_preserves_not_jmp.
    + by eapply estep_preserves_not_jmp.
  - exfalso. move:(cstep_not_val H0)=>Hn.
    by eapply (is_jmp_jstep_false []).
Qed.

Lemma same_type_encode_inj σ:
  ∀ t v v' p,
    typeof v t → typeof v' t →
    readbytes p (encode_val v) σ →
    readbytes p (encode_val v') σ →
    v = v'.
Proof.
  induction t;
    intros v v' p Htv Htv';
    inversion Htv; inversion Htv'=>//; subst;
    intros Hv1 Hv2; subst; destruct p; simpl in Hv1, Hv2.
  - rewrite Byte.repr_unsigned in Hv2, Hv1.
    destruct_ands. rewrite H in H1.
    inversion H1. by rewrite Byte.repr_unsigned.
  - destruct_ands.
    admit.
  - destruct_ands.
    by rewrite H in H4.
  - destruct_ands.
    by rewrite H in H4.
  - destruct_ands.
    rewrite H in H4. by inversion H4.
  - f_equal.
    + eapply IHt1=>//; by eapply readbytes_segment.
    + eapply IHt2=>//.
      * by eapply readbytes_segment_2.
      * replace (length (encode_val v1)) with
        (length (encode_val v0)).
        by eapply readbytes_segment_2.
        { rewrite -(typeof_preserves_size v0 t1)=>//.
          rewrite -(typeof_preserves_size v1 t1)=>//. }
Admitted. (* Hairy arithmetic -- should be right. Documented *)

Definition step e σ e' σ' (efs: list expr) := cstep e σ e' σ' ∧ efs = [].

Lemma step_not_val e σ e' σ' efs:
  step e σ e' σ' efs → to_val e = None.
Proof. destruct 1. by eapply cstep_not_val. Qed.

Definition clang_lang :=
  Language expr val state Evalue to_val step to_of_val of_to_val step_not_val.

Ltac absurd_jstep' :=
  match goal with
  | [ HF: fill_ectxs _ _ = ?E |- _ ] =>
    replace E with (fill_ectxs E []) in HF=>//; apply cont_inj in HF=>//;
      by destruct HF; auto
  end.

Ltac absurd_jstep Hjs :=
  inversion Hjs; simplify_eq;
  [ match goal with
    | [ HU: unfill _ _ , HF: fill_ectxs _ _ = _ |- _ ] =>
        by rewrite /unfill HF /= in HU
    end
  | absurd_jstep' ].

Ltac atomic_step H :=
  inversion H; subst;
  [ match goal with
    | [ HE: estep _ _ _ _ |- _ ] =>
      inversion HE; subst;
      [ idtac | exfalso; by escape_false ]
    end
  | match goal with
    | [ HJ : jstep _ _ _ _ _ |- _ ] => absurd_jstep HJ
    end
  ].

Definition clang_atomic (e: expr) :=
  match e with
  | ECAS_typed t e1 e2 e3 => bool_decide (is_loc e1 ∧ is_val e2 ∧ is_val e3)
  | Ederef_typed t e => bool_decide (is_loc e)
  | Ealloc t e => bool_decide (is_val e)
  | Eassign e1 e2 => bool_decide (is_loc e1 ∧ is_val e2)
  | _ => false
  end.

Lemma atomic_enf e:
  clang_atomic e → language.atomic (e: language.expr clang_lang).
Proof.
  - intros ????? [Hcs ?]. apply language.val_irreducible.
    destruct e=>//.
    + destruct e1=>//. destruct v=>//.
      destruct e2=>//. destruct e3=>//.
      inversion_cstep_as Hes Hjs.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
    + destruct e=>//. inversion_cstep_as Hes Hjs.
      inversion_cstep_as Hes Hjs.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
      { absurd_jstep Hjs. }
    + destruct e=>//. inversion_cstep_as Hes Hjs.
      inversion_cstep_as Hes Hjs.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
      { absurd_jstep Hjs. }
    + destruct e1=>//. destruct v=>//. destruct e2=>//.
      inversion_cstep_as Hes Hjs.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
Qed. (* FIXME: prettify the proof *)

Lemma empty_ctx e: e = fill_ectxs e []. done. Qed.

Ltac rewrite_empty_ctx :=
  match goal with
  | [ H : fill_ectxs _ _ = ?E |- _ ] =>
    erewrite empty_ctx in H
  | [ H : fill_expr _ _ = ?E |- _ ] =>
    erewrite empty_ctx in H
  end.

Ltac fill_enf_neq :=
  match goal with
  | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _ ] =>
    apply cont_inj in H=>//; auto; by destruct H as [? ?]
  | [ H : fill_ectxs _ _ = _ |- _ ] =>
    rewrite_empty_ctx; apply cont_inj in H=>//; auto; by destruct H as [? ?]
  | _ => done
  end.

Fixpoint default_val (t: type) :=
  match t with
    | Tvoid => Vvoid
    | Tnull => Vnull
    | Tint8 => Vint8 $ Byte.repr 0
    | Tint32 => Vint32 $ Int.repr 0
    | Tptr _ => Vnull
    | Tprod t1 t2 => Vpair (default_val t1) (default_val t2)
  end.

Lemma default_val_types (t: type) :
  typeof (default_val t) t.
Proof. induction t; crush. Qed.
