(** Language definition **)

From iris.base_logic Require Export gen_heap big_op.
From iris.algebra Require Import gmap.
From iris_c.lib Require Export smap prelude.
From iris_c.program_logic Require Export language.
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
| Evar (x: string)
| Elet (t: type) (x: ident) (ex ebody: expr)
| ECAS (t: type) (e1 e2 e3: expr)
| Ebinop (op: bop) (e1: expr) (e2: expr)
| Ederef (e: expr)
| Ederef_typed (t: type) (e: expr)
| Eaddrof (e: expr)
| Efst (e: expr)
| Esnd (e: expr)
| Ecall (t: type) (fid: ident) (args: list expr)
| Ealloc (t: type) (e: expr)
| Eassign (lhs: expr) (rhs: expr)
| Eif (c e1 e2: expr)
| Ewhile (c e: expr)
| Erete (e: expr)
| Eseq (e1 e2: expr)
| Ebreak
| Econtinue
| Efork (t: type) (fid: ident) (args: list expr).

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
| EKfork (t: type) (fid: ident) (vargs: list val) (args: list expr)
| EKalloc (t: type)
| EKassignr (rhs: expr)
| EKassignl (lhs: addr)
| EKif (s1 s2: expr)
| EKrete
| EKseq (s: expr).

Definition env := smap type.

Fixpoint type_infer (ev: env) (e: expr) : option type :=
  match e with
    | Evalue v => Some (type_infer_v v)
    | Evar x => sget x ev
    | Ebinop _ e1 _ => type_infer ev e1 (* FIXME *)
    | ECAS t _ e1 _ => Some t
    | Elet t x ex ebody => type_infer (sset x t ev) ebody
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
    | Ecall t f args => Some t
    | Ealloc t _ => Some (Tptr t)
    | Efork _ _ _ => Some Tvoid
    | Eassign _ _ => Some Tvoid
    | Eif _ _ _ => Some Tvoid
    | Ewhile _ _ => Some Tvoid
    | Ebreak => Some Tvoid
    | Econtinue => Some Tvoid
    | Erete _ => Some Tvoid
    | Eseq _ e2 => type_infer ev e2
  end.

Definition fill_expr (e : expr) (Ke : exprctx) : expr :=
  match Ke with
    | EKbinopr op re => Ebinop op e re
    | EKbinopl op lv => Ebinop op (Evalue lv) e
    | EKCASl t e1 e2 => ECAS t e e1 e2
    | EKCASm t l0 e2 => ECAS t (Evalue (Vptr l0)) e e2
    | EKCASr t l0 v1 => ECAS t (Evalue (Vptr l0)) (Evalue v1) e
    | EKderef_typed t => Ederef_typed t e
    | EKaddrof => Eaddrof e
    | EKfst => Efst e
    | EKsnd => Esnd e
    | EKcall t f vargs args => Ecall t f (map Evalue vargs ++ e :: args)
    | EKfork t f vargs args => Efork t f (map Evalue vargs ++ e :: args)
    | EKalloc t => Ealloc t e
    | EKassignr rhs => Eassign e rhs
    | EKassignl lhs => Eassign (Evalue (Vptr lhs)) e
    | EKif s1 s2 => Eif e s1 s2
    | EKrete => Erete e
    | EKseq s => Eseq e s
    | EKlet t x ebody => Elet t x e ebody
  end.

Definition fill_ectxs := foldr (λ x y, fill_expr y x).
Definition heap := gmap addr byteval.
Definition text := gmap ident function.
Definition cont := list exprctx.
Inductive ctx :=
| Kcall (K: cont)
| Kwhile (c e: expr) (K: cont).
Definition stack := list ctx.

Record state :=
  State {
      s_heap : heap;
      s_text : text
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
  | Ebreak => Some e
  | Econtinue => Some e
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
  | Ecall t f args => Ecall t f <$>
                            lift_list_option
                            (map (resolve_rhs ev x vx tx) args)
  | Efork t f args => Efork t f <$>
                            lift_list_option
                            (map (resolve_rhs ev x vx tx) args)
  | Eassign e1 e2 => Eassign e1 <$> resolve_rhs ev x vx tx e2
  | Eif e s1 s2 =>
    match resolve_rhs ev x vx tx e,
          resolve_rhs ev x vx tx s1,
          resolve_rhs ev x vx tx s2 with
    | Some e', Some s1', Some s2' => Some $ Eif e' s1' s2'
    | _, _, _ => None
    end
  | Ewhile c e =>
    match resolve_rhs ev x vx tx c, resolve_rhs ev x vx tx e with
    | Some c', Some e' => Some $ Ewhile c' e'
    | _, _ => None
    end
  | Erete e => Erete <$> resolve_rhs ev x vx tx e
  | Eseq s1 s2 =>
    match resolve_rhs ev x vx tx s1, resolve_rhs ev x vx tx s2 with
    | Some s1', Some s2' => Some (Eseq s1' s2')
    | _, _ => None
    end
  | ECAS t e1 e2 e3 =>
    match resolve_rhs ev x vx tx e1,
          resolve_rhs ev x vx tx e2,
          resolve_rhs ev x vx tx e3 with
    | Some e1', Some e2', Some e3' => Some (ECAS t e1' e2' e3')
    | _, _, _ => None
    end
  | Elet t y ey ebody =>
    if bool_decide (x = y)
    then Some e
    else match resolve_rhs ev x vx tx ey with
         | Some ey' => Elet t y ey' <$> (resolve_rhs (sset y t ev) x vx tx ebody)
         | _ => None
         end
  end.

Fixpoint resolve_lhs_inner (ev: env) (x: ident)
                           (vx: val) (tx: type) (e: expr) : option expr :=
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
    | Ewhile c e =>
      match resolve_lhs_outer ev x vx tx c,
            resolve_lhs_outer ev x vx tx e with
        | Some c', Some e' =>
          Some $ Ewhile c' e'
        | _, _ => None
      end
    | Eseq s1 s2 =>
      match resolve_lhs_outer ev x vx tx s1, resolve_lhs_outer ev x vx tx s2 with
        | Some s1', Some s2' => Some (Eseq s1' s2')
        | _, _ => None
      end
    | Elet t y ey ebody =>
      if bool_decide (x = y)
      then Some e
      else Elet t y ey <$> (resolve_lhs_outer (sset y t ev) x vx tx ebody)
    | _ => Some e
  end.

Definition instantiate_let (x: ident) (vx: val) (tx: type) (s: expr) : option expr :=
  (resolve_rhs (ssig x tx) x vx tx s ≫= resolve_lhs_outer (ssig x tx) x vx tx).

Fixpoint is_jmp (e: expr) :=
  match e with
    | Ecall _ _ _ => true
    | Erete _ => true
    | Ewhile _ _ => true
    | Ebreak => true
    | Econtinue => true
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
    | ECAS t e1 e2 e3 => is_jmp e1 || is_jmp e2 || is_jmp e3
    | Elet t x ex ebody => is_jmp ex || is_jmp ebody
    | Efork t f es => existsb is_jmp es
    | _ => false
  end.

Inductive jnf: expr → Prop :=
| JNFcall: ∀ t f vs, jnf (Ecall t f (map Evalue vs))
| JNFrete: ∀ v, jnf (Erete (Evalue v)).

Inductive wnf: expr → Prop :=
| WNFwhile: ∀ c e, wnf (Ewhile c e)
| WNFbreak: wnf Ebreak
| WNFcontinue: wnf Econtinue.

Global Hint Constructors jnf wnf.

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

Lemma exists_is_jmp_false vs:
  existsb is_jmp (map Evalue vs) = false.
Proof. induction vs; crush. Qed.

Lemma is_jmp_rec' e K:
  is_jmp (fill_expr e K) = false → is_jmp e = false.
Proof.
  induction K=>//; simpl; intros; try solve_is_jmp_false.
  rewrite existsb_app exists_is_jmp_false in H.
  simpl in H. solve_is_jmp_false.
Qed.

Lemma is_jmp_rec e ks:
  is_jmp (fill_ectxs e ks) = false → is_jmp e = false.
Proof. induction ks=>//. simpl; intros. apply is_jmp_rec' in H. auto. Qed.

Lemma is_jmp_out' e e' K:
  is_jmp e' = false →
  is_jmp (fill_expr e K) = false →
  is_jmp (fill_expr e' K) = false.
Proof.
  induction K=>//; simpl; intros; try by solve_is_jmp_false=>//.
  rewrite existsb_app exists_is_jmp_false in H0. simpl in H0.
  rewrite existsb_app exists_is_jmp_false.
  simpl. rewrite H. simpl. destruct (is_jmp e); destruct (existsb is_jmp args)=>//.
Qed.

Lemma is_jmp_out e e' K:
  is_jmp e' = false →
  is_jmp (fill_ectxs e K) = false →
  is_jmp (fill_ectxs e' K) = false.
Proof.
  induction K=>//. simpl. intros. eapply is_jmp_out'=>//.
  apply IHK=>//. eapply is_jmp_rec'=>//.
Qed.

Fixpoint let_params (vs: list val) (params: decls) e : option expr :=
  match vs, params with
  | v::vs', (x, tx)::ps' => Elet tx x (Ealloc tx (Evalue v))
                                 <$> let_params vs' ps' e
  | [], [] => Some e
  | _, _ => None
  end.

Inductive estep : text → expr → heap → expr → heap → list expr → Prop :=
| ESbinop: ∀ Γ lv rv op σ v',
             evalbop op lv rv = Some v' →
             estep Γ (Ebinop op (Evalue lv) (Evalue rv)) σ
                     (Evalue v') σ []
| ESderef_typed:
    ∀ σ l v t Γ,
      typeof v t →
      readbytes l (encode_val v) σ →
      estep Γ (Ederef_typed t (Evalue (Vptr l))) σ
             (Evalue v) σ []
| ESfst:
    ∀ v1 v2 σ Γ,
      estep Γ (Efst (Evalue (Vpair v1 v2))) σ (Evalue v1) σ []
| ESsnd:
    ∀ v1 v2 σ Γ,
      estep Γ (Esnd (Evalue (Vpair v1 v2))) σ (Evalue v2) σ []
| ESalloc:
    ∀ t v σ b o Γ,
      typeof v t →
      (∀ o', σ !! (b, o') = None) →
      estep Γ (Ealloc t (Evalue v)) σ (Evalue (Vptr (b, o)))
              (alloc_heap (b, o) v σ) []
| ESassign:
    ∀ l v σ Γ,
      estep Γ (Eassign (Evalue (Vptr l)) (Evalue v))
            σ (Evalue Vvoid)
            (storebytes l (encode_val v) σ) []
| ESseq: ∀ s v σ Γ, estep Γ (Eseq (Evalue v) s) σ s σ []
| ESCASFail Γ l t v1 v2 vl σ :
    typeof v1 t →
    typeof v2 t →
    typeof vl t →
    readbytes l (encode_val vl) σ → vl ≠ v1 →
    estep Γ (ECAS t (Evalue (Vptr l)) (Evalue v1) (Evalue v2)) σ
            (Evalue vfalse) σ []
| ESCASSuc Γ l t v1 v2 σ :
    typeof v1 t →
    typeof v2 t →
    readbytes l (encode_val v1) σ →
    estep Γ (ECAS t (Evalue (Vptr l)) (Evalue v1) (Evalue v2)) σ
            (Evalue vtrue) (storebytes l (encode_val v2) σ) []
| ESlet t x xv e e' σ Γ:
    instantiate_let x xv t e = Some e' →
    estep Γ (Elet t x (Evalue xv) e) σ e' σ []
| ESifTrue e1 e2 σ Γ:
    estep Γ (Eif (Evalue vtrue) e1 e2) σ e1 σ []
| ESifFalse e1 e2 σ Γ:
    estep Γ (Eif (Evalue vfalse) e1 e2) σ e2 σ []
| ESfork:
    ∀ Γ σ f e e' vs retty params,
      Γ !! f = Some (Function retty params e) →
      let_params vs params e = Some e' →
      estep Γ (Efork retty f $ map Evalue vs) σ (Evalue Vvoid) σ [e']
| ESbind':
    ∀ e e' σ σ' k kes efs Γ,
      is_jmp e = false →
      estep Γ e σ e' σ' efs →
      estep Γ (fill_ectxs e (k::kes)) σ (fill_ectxs e' (k::kes)) σ' efs.
(* !!!!!!!!!!!:
   NEVER add new semantic rules after ESbind',
   which would break everything
*)

Lemma ESbind:
    ∀ kes e e' σ σ' Γ efs,
      is_jmp e = false →
      estep Γ e σ e' σ' efs →
      estep Γ (fill_ectxs e kes) σ (fill_ectxs e' kes) σ' efs.
Proof. induction kes=>//. intros. apply ESbind'=>//. Qed.

Lemma estep_not_val {e σ e' σ' G efs}:
  estep G e σ e' σ' efs → to_val e = None.
Proof. induction 1=>//. by apply fill_ectxs_not_val. Qed.

Definition is_val e := is_some (to_val e).

Lemma to_val_is_val e:
  to_val e = None ↔ is_val e = false.
Proof. induction e; crush. Qed.

Lemma fill_ectxs_not_is_val Kes:
  ∀ e, is_val (fill_ectxs e Kes) = true → is_val e = true.
Proof.
  intros. destruct (is_val e) eqn:Heqn=>//.
  apply to_val_is_val in Heqn.
  apply (fill_ectxs_not_val Kes) in Heqn.
  apply to_val_is_val in Heqn. rewrite H in Heqn. done.
Qed.

Lemma forall_is_val vs:
  forallb is_val (map Evalue vs) = true.
Proof. by induction vs=>//. Qed.

Definition is_loc e :=
  match to_val e with
    | Some (Vptr _) => true
    | _ => false
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
  | LNFCAS: ∀ l t v1 v2, lnf (ECAS t (Evalue (Vptr l)) (Evalue v1) (Evalue v2))
  | LNFlet: ∀ t x v e2, lnf (Elet t x (Evalue v) e2)
  | LNFfork: ∀ f t es, lnf (Efork f t $ map Evalue es).

Inductive enf: expr → Prop :=
| jnf_enf: ∀ e, jnf e → enf e
| lnf_enf: ∀ e, lnf e → enf e
| wnf_enf: ∀ e, wnf e → enf e.

Global Hint Constructors lnf enf.

Definition UF (e: expr) (eh: expr) (k: cont) : Prop :=
  fill_ectxs eh k = e.

Lemma enf_not_val e: enf e → to_val e = None.
Proof. induction e; crush. inversion H; inversion H0. Qed.

Lemma fill_app e K K': fill_ectxs (fill_ectxs e K) K' = fill_ectxs e (K' ++ K).
Proof. induction K'=>//. simpl. by rewrite IHK'. Qed.


Lemma lnf_not_val e: lnf e → is_val e = false.
Proof. inversion 1=>//. Qed.

Lemma jnf_not_val e: jnf e → is_val e = false.
Proof. inversion 1=>//. Qed.

Lemma vs_map: ∀ vs vs' a args,
  map Evalue vs = map Evalue vs' ++ a :: args → is_val a = true.
Proof.
  induction vs.
  - simpl. intros. destruct vs'=>//.
  - simpl. intros.
    destruct vs'.
    + simpl in *. by simplify_eq.
    + simpl in *. simplify_eq. by eapply IHvs.
Qed.

Lemma vs_map2: ∀ vs vs' e e' es es',
  to_val e = None → to_val e' = None →
  map Evalue vs ++ e :: es = map Evalue vs' ++ e' :: es' →
  vs = vs' ∧ e = e' ∧ es = es'.
Proof.
  induction vs; intros; destruct vs'; simpl in *; simplify_eq=>//.
  eapply IHvs in H2=>//.
  by destruct_ands.
Qed.

Lemma fill_uninj_val e ks v1:
  fill_ectxs e ks = Evalue v1 → e = Evalue v1 ∧ ks = [].
Proof.
  destruct ks=>//.
  simpl. intros.
  destruct e0=>//.
Qed.

Ltac solve_val_fill NF :=
  simpl in *; simplify_eq;
  match goal with
    | [ H : fill_ectxs _ _ = Evalue _ |- _] =>
      apply fill_uninj_val in H; destruct_ands;
        match goal with
        | [ H: NF (Evalue _) |- _ ] => inversion H
        end
    end.

Lemma fill_expr_inj e e' k k':
  to_val e = None → to_val e' = None →
  fill_expr e k = fill_expr e' k' -> e = e' ∧ k = k'.
Proof.
  destruct k; destruct k'; intros; simpl in *; try by simplify_eq.
  - simplify_eq. apply vs_map2 in H3=>//. by destruct_ands.
  - simplify_eq. apply vs_map2 in H3=>//. by destruct_ands.
Qed.

Lemma weak_cont_inj': ∀ ks e e',
  to_val e = None → enf e' → fill_expr e ks = e' → False.
Proof.
  destruct ks=>//;
    (intros; simpl in *; subst;
    inversion H0; try by inversion H1; inversion H1
    ; try by subst).
  - inversion H1. subst.
    apply vs_map in H6. apply to_val_is_val in H. by rewrite H in H6.
  - inversion H1. subst.
    apply vs_map in H6. apply to_val_is_val in H. by rewrite H in H6.
Qed.

Lemma weak_cont_inj: ∀ ks e e',
  enf e → enf e' → fill_ectxs e ks = e' → e = e' ∧ ks = [].
Proof.
  induction ks=>//.
  intros. simpl in *. apply weak_cont_inj' in H1=>//.
  by apply fill_ectxs_not_val, enf_not_val.
Qed.
  
Lemma cont_inj: ∀ kes kes' e e',
  enf e → enf e' →
  fill_ectxs e kes = fill_ectxs e' kes' → e = e' ∧ kes = kes'.
Proof.
  induction kes; induction kes'=>//.
  - intros. replace (fill_ectxs e []) with e in H1=>//.
    symmetry in H1. apply weak_cont_inj in H1=>//.
    destruct_ands; done.
  - intros. replace (fill_ectxs e' []) with e' in H1=>//.
    apply weak_cont_inj in H1=>//.
  - intros.
    simpl in H1. apply fill_expr_inj in H1.
    + destruct_ands. apply IHkes in H1=>//.
      by destruct_ands.
    + by apply fill_ectxs_not_val, enf_not_val.
    + by apply fill_ectxs_not_val, enf_not_val.
Qed.

Lemma fill_not_enf e k:
  is_val e = false → enf (fill_expr e k) → False.
Proof. induction k=>//; simpl; intros H1 H2;
       try (inversion H2; by subst);
       try (inversion H2;
            [ inversion H
            | subst; inversion H; by subst
            | subst; inversion H; by subst ]).
       - assert (forallb is_val (map Evalue vargs ++ e :: args) = true) as Hcontra.
         { subst. rewrite -H6. apply forall_is_val. }
         rewrite forallb_app in Hcontra.
         replace (e::args) with ([e] ++ args) in Hcontra; last done.
         rewrite forallb_app in Hcontra. simpl in Hcontra. rewrite H1 in Hcontra.
           by rewrite andb_false_r in Hcontra.
       - inversion H2; first inversion H.
         + inversion H. subst.
           assert (forallb is_val (map Evalue vargs ++ e :: args) = true) as Hcontra.
           { subst. rewrite -H6. apply forall_is_val. }
           rewrite forallb_app in Hcontra.
           replace (e::args) with ([e] ++ args) in Hcontra; last done.
           rewrite forallb_app in Hcontra. simpl in Hcontra. rewrite H1 in Hcontra.
           by rewrite andb_false_r in Hcontra.
         + inversion H.
       - by subst.
Qed.

Lemma escape_false {e a e' a2 kes k0 e'' G efs}:
  estep G e a e' a2 efs →
  fill_expr (fill_ectxs e kes) k0 = e'' → enf e'' → False.
Proof.
  intros. subst. eapply fill_not_enf=>//.
  apply to_val_is_val, fill_ectxs_not_val. by eapply estep_not_val.
Qed.

Lemma escape_false' {e a e' a2 kes k0 G efs}:
  estep G e a e' a2 efs →
  enf (fill_expr (fill_ectxs e kes) k0) → False.
Proof. intros Hes Henf. eapply escape_false=>//. Qed.

Ltac gen_eq H E1 E2 KS :=
  replace E1 with (fill_ectxs E1 []) in H; last done;
  assert (E1 = E2 ∧ [] = KS) as [? ?];
  [ apply cont_inj=>// | subst; clear H ].

Lemma fill_cons e K K': fill_expr (fill_ectxs e K) K' = fill_ectxs e (K' :: K).
Proof. induction K'=>//. Qed.

Lemma size_ind (P: cont → Prop):
  (∀ ks, (∀ ks', length ks' < length ks → P ks')%nat → P ks) →
  (∀ ks, P ks).
Proof.
  intros Hstep ks.
  apply Hstep.
  assert (∀ n, ∀ ks', (length ks' < n)%nat → P ks') as G.
  { induction n.
    + intros ks' H. inversion H.
    + intros ks' H. apply Hstep. intros ??.
      apply IHn. omega. }
  apply G.
Qed.

Lemma unfill_segment: ∀ ks ks' e eh,
  to_val e = None → enf eh →
  fill_ectxs e ks = fill_ectxs eh ks' →
  ∃ ks'', ks' = ks ++ ks'' ∧ e = fill_ectxs eh ks''.
Proof.
  induction ks.
  - intros. simpl in *. subst. eauto.
  - intros.
    destruct ks'.
    + simpl in *. subst.
      apply fill_not_enf in H0=>//.
      by apply to_val_is_val, fill_ectxs_not_val.
    + simpl in *. apply fill_expr_inj in H1.
      * destruct_ands.
        apply IHks in H1=>//.
        destruct H1 as [? [? ?]].
        subst. eauto.
      * by apply fill_ectxs_not_val.
      * by apply fill_ectxs_not_val, enf_not_val.
Qed.

Arguments unfill_segment {_ _ _ _} _ _ _.

Ltac inversion_cstep Hnf tac :=
  match goal with
      | [ H : estep _ (fill_ectxs _ _) _ _ _ _ |- _ ] => (
          inversion H=>//;
          try (match goal with
               | [ H2 : fill_expr (fill_ectxs ?E _) _ =
                        fill_ectxs ?E2 ?KS |- _ ] =>
                 rewrite fill_cons in H2; subst;
                 match goal with
                 | [ H3 : estep _ E _ _ _ _ |- _ ] =>
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
      (∀ e2 G efs,
         estep G (fill_ectxs eh1 K) σ1 e2 σ2 efs →
         ∃ eh2, estep G eh1 σ1 eh2 σ2 efs ∧ e2 = fill_ectxs eh2 K
      )
  in ∀ K, P K.
Proof.
  intros Hnf P. apply (size_ind P).
  unfold P. intros ks Hind e2 G efs Hes.
  inversion_cstep Hnf idtac.
  apply (Hind K') in H2.
  + destruct H2 as [eh2 [? ?]]. subst.
    exists eh2. split=>//. by rewrite fill_app.
  + rewrite app_length. simpl. omega.
Qed.

Lemma focus_estep_inv'' {eh1 σ1 σ2}:
  enf eh1 →
  ∀ K e2 G efs,
    estep G (fill_ectxs eh1 K) σ1 e2 σ2 efs →
    ∃ eh2, estep G eh1 σ1 eh2 σ2 efs ∧ e2 = fill_ectxs eh2 K.
Proof. intros H. move: (focus_estep_inv' eh1 σ1 σ2 H) => /= H'. done. Qed.

Definition wellformed e := ∃ K eh, e = fill_ectxs eh K ∧ enf eh.

Lemma fill_wellformed e ks:
  to_val e = None → wellformed (fill_ectxs e ks) → wellformed e.
Proof.
  intros H1 H2. destruct ks=>//.
  inversion H2 as [? [? [? ?]]].
  apply unfill_segment in H=>//.
  destruct H as [? [? ?]].
  eexists _, _. split=>//.
Qed.

Lemma wf_not_val e: wellformed e → to_val e = None.
Proof.
  intros [? [? [? ?]]].
  subst. apply fill_ectxs_not_val. by apply enf_not_val.
Qed.

Axiom wellformed_estep: ∀ e1 σ1 e2 σ2 G efs,
  estep G e1 σ1 e2 σ2 efs → wellformed e1.

Arguments wellformed_estep {_ _ _ _ _ _} _.

Lemma focus_estep_inv {e1 σ1 e2 σ2 G efs}:
  estep G e1 σ1 e2 σ2 efs →
  ∃ e1' e2' K, enf e1' ∧ e1 = fill_ectxs e1' K ∧
               estep G e1' σ1 e2' σ2 efs ∧ e2 = fill_ectxs e2' K.
Proof.
  intros H. move: (wellformed_estep H) => [K [eh1 [? H']]].
  subst. exists eh1.
  edestruct (@focus_estep_inv'' eh1 σ1 σ2 H' K e2) as [e' [? ?]]=>//.
  eexists _, _. split=>//; split=>//.
Qed.

Tactic Notation "escape_false" :=
  exfalso;
  match goal with
  | [ Hes: estep _ ?e ?a ?e' ?a2 _,
      Heq: fill_expr (fill_ectxs ?e ?kes) ?k0 = ?e'' |- _ ] =>
      by eapply (escape_false Hes Heq)=>//; auto
  | [ Hes: estep _ ?e ?a ?e' ?a2 _,
      Henf: enf (fill_expr (fill_ectxs ?e ?kes) ?k) |- _ ] =>
      by eapply (escape_false' Hes Henf)=>//; auto
  end.

Lemma estep_call_false t f vs σ1 e' σ2 G efs:
  estep G (Ecall t f (map Evalue vs)) σ1 e' σ2 efs → False.
Proof. inversion 1. subst. escape_false. Qed.

Lemma estep_ret_false v σ1 e' σ2 G efs:
  estep G (Erete (Evalue v)) σ1 e' σ2 efs → False.
Proof. inversion 1. subst. escape_false. Qed.

Lemma fill_estep_false' e σ σ':
  jnf e →
  let P K :=
      (∀ e' G efs, estep G (fill_ectxs e K) σ e' σ' efs → False)
  in ∀ K, P K.
Proof.
  intros Hjn P. assert (enf e) as Henf; first by apply jnf_enf.
  apply (size_ind P).
  unfold P. intros ks Hind e' G efs Hes.
  inversion_cstep Henf ltac:(inversion Hjn).
  apply (Hind K') in H2=>//.
  rewrite app_length. simpl. omega.
Qed.

Lemma fill_estep_false {e kes e' σ σ' G efs}:
  jnf e → estep G (fill_ectxs e kes) σ e' σ' efs → False.
Proof. intros H. move: (fill_estep_false' e σ σ' H kes e' G efs) => /= H'. done. Qed.

Lemma wf_not_val_ind:
  ∀ P: expr → Prop,
    (∀ e, enf e → P e) →
    (∀ e ks, to_val e = None → P e → P (fill_ectxs e ks)) →
    (∀ e, wellformed e → P e).
Proof.
  intros P Henf Hind e Hwf.
  destruct Hwf as [K [eh [ ? ?]]].
  subst. apply Hind.
  - by apply enf_not_val.
  - by apply Henf.
Qed.

Lemma not_val_ind'':
  ∀ P: expr → Prop,
    (∀ e, enf e → P e) →
    (∀ e ks, enf e →
             (∀ ks', length ks' < length ks →
                     P (fill_ectxs e ks'))%nat → P (fill_ectxs e ks)) →
    (∀ e, wellformed e → P e).
Proof.
  intros.
  destruct H1 as [? [? [? ?]]].
  subst. apply (size_ind (fun x => P (fill_ectxs x0 x))).
  intros. apply H0=>//.
Qed.

Lemma fill_estep_inv':
  let P e :=
    (∀ e' σ σ' ks G efs,
       is_jmp e = false →
       estep G (fill_ectxs e ks) σ e' σ' efs →
       ∃ e'', estep G e σ e'' σ' efs ∧ e' = fill_ectxs e'' ks)
  in ∀ e, wellformed e → P e.
Proof.
  intros P. apply (wf_not_val_ind P).
  - unfold P. intros e Henf e' σ σ' ks G efs Hnj Hes.
    eapply focus_estep_inv in Hes.
    destruct Hes as (e1'&e2'&K&Henf'&Heq&Hes'&Heq'). subst.
    eapply cont_inj in Heq=>//.
    destruct Heq. subst. eauto.
  - unfold P. intros e ks Hnv Hind e' σ σ' ks' G efs Hnj Hes.
    rewrite fill_app in Hes.
    apply Hind in Hes; last by eapply is_jmp_rec.
    destruct Hes as (e''&Hes''&Heq').
    exists (fill_ectxs e'' ks).
    split.
    { apply ESbind=>//. by eapply is_jmp_rec. }
    { by rewrite fill_app. }
Qed.

Lemma fill_estep_inv {e ks a a1 a2 G efs}:
  to_val e = None →
  is_jmp e = false →
  estep G (fill_ectxs e ks) a a1 a2 efs →
  ∃ e', estep G e a e' a2 efs ∧ a1 = fill_ectxs e' ks.
Proof. move: fill_estep_inv' => /= H. intros.
       move:(wellformed_estep H2)=>?.
       apply H=>//.
       by eapply fill_wellformed.
Qed.

Lemma cont_incl':
  let P e' :=
      (∀ e kes kes',
        enf e →
        fill_ectxs e kes = fill_ectxs e' kes' →
        ∃ kes'', e' = fill_ectxs e kes'')
  in ∀ e', wellformed e' → P e'.
Proof.
  intros P. apply (wf_not_val_ind P).
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
  wellformed e' →
  fill_ectxs e kes = fill_ectxs e' kes' →
  ∃ kes'', e' = fill_ectxs e kes''.
Proof. move: cont_incl' => /= H. intros. by eapply H. Qed.

Definition not_Kcall (K: ctx) :=
  match K with
  | Kcall _ => false
  | _ => true
  end.

Definition not_Kwhile (K: ctx) :=
  match K with
  | Kwhile _ _ _ => false
  | _ => true
  end.

Inductive jstep: text → expr → stack → expr → stack → Prop :=
| JSrete:
    ∀ t v k k' ks KS,
      forallb not_Kcall KS = true →
      jstep t
            (fill_ectxs (Erete (Evalue v)) k') (KS ++ Kcall k :: ks)
            (fill_ectxs (Evalue v) k) ks
| JScall:
    ∀ vs e' retty params f_body f t k ks,
      t !! f = Some (Function retty params f_body) →
      let_params vs params f_body = Some e' →
      jstep t (fill_ectxs (Ecall retty f (map Evalue vs)) k) ks
            e' (Kcall k::ks).

Inductive wstep: expr → stack → expr → stack → Prop :=
| WSwhile:
    ∀ c k ks e,
      wstep (fill_ectxs (Ewhile c e) k) ks
            (Eif c (Eseq e Econtinue) Ebreak)
            (Kwhile c e k::ks)
| WSbreak:
    ∀ c e k k' ks KS,
      forallb not_Kwhile KS = true →
      wstep (fill_ectxs Ebreak k') (KS ++ Kwhile c e k :: ks)
            (fill_ectxs (Evalue Vvoid) k) ks
| WScontinue:
    ∀ k' KS c e k ks,
      forallb not_Kwhile KS = true →
      wstep (fill_ectxs Econtinue k')
            (KS ++ Kwhile c e k :: ks)
            (fill_ectxs (Ewhile c e) k) ks.

Lemma fill_wstep_false' e σ σ':
  jnf e →
  let P K :=
      (∀ e', wstep (fill_ectxs e K) σ e' σ' → False)
  in ∀ K, P K.
Proof.
  intros Hjn P. assert (enf e) as Henf; first by apply jnf_enf.
  apply (size_ind P).
  unfold P. intros ks Hind e' Hes.
  inversion Hjn; subst;
    inversion Hes; subst;
      match goal with
      | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _] =>
        apply cont_inj in H=>//
      end;
      (by destruct_ands ||
       by apply wnf_enf).
Qed.

Lemma fill_wstep_false {e kes e' σ σ'}:
  jnf e → wstep (fill_ectxs e kes) σ e' σ' → False.
Proof.
  intros H. move: (fill_wstep_false' e σ σ' H kes e') => /= H'. apply H'.
Qed.

Lemma wfill_jstep_false' e σ σ':
  wnf e →
  let P K :=
      (∀ e' t, jstep t (fill_ectxs e K) σ e' σ' → False)
  in ∀ K, P K.
Proof.
  intros Hwn P. assert (enf e) as Henf; first by apply wnf_enf.
  apply (size_ind P).
  unfold P. intros ks Hind e' t Hes.
  inversion Hwn; subst;
    inversion Hes; subst;
      match goal with
      | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _] =>
        apply cont_inj in H=>//
      end;
      (by destruct_ands ||
       by apply jnf_enf).
Qed.

Lemma wfill_jstep_false {e kes e' σ σ' t}:
  wnf e → jstep t (fill_ectxs e kes) σ e' σ' → False.
Proof.
  intros H. move: (wfill_jstep_false' e σ σ' H kes e') => /= H'. apply H'.
Qed.

Lemma wfill_estep_false' e σ σ':
  wnf e →
  let P K :=
      (∀ e' G efs, estep G (fill_ectxs e K) σ e' σ' efs → False)
  in ∀ K, P K.
Proof.
  intros Hwn P. assert (enf e) as Henf; first by apply wnf_enf.
  apply (size_ind P).
  unfold P. intros ks Hind e' G efs Hes.
  inversion_cstep Henf ltac:(inversion Hwn).
  apply (Hind K') in H2=>//.
  rewrite app_length. simpl. omega.
Qed.

Lemma wfill_estep_false {e kes e' σ σ' G efs}:
  wnf e → estep G (fill_ectxs e kes) σ e' σ' efs → False.
Proof. intros H. by move: (wfill_estep_false' e σ σ' H kes e' G efs) => /= H'. Qed.

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.

Definition local_state := stack.

Inductive cstep:
  expr → local_state → state → expr → local_state → state → list expr → Prop :=
| CSestep:
    ∀ s t e h e' h' efs,
      estep t e h e' h' efs →
      cstep e s (State h t) e' s (State h' t) efs
| CSjstep:
    ∀ e e' h t s s',
      jstep t e s e' s' →
      cstep e s (State h t) e' s' (State h t) []
| CSwstep:
    ∀ σ e s e' s',
      wstep e s e' s' →
      cstep e s σ e' s' σ [].

Axiom wellformed_cstep: ∀ e1 l1 σ1 e2 l2 σ2 efs,
  cstep e1 l1 σ1 e2 l2 σ2 efs → wellformed e1.
Arguments wellformed_cstep {_ _ _ _ _ _ _} _.

Ltac inversion_estep :=
  match goal with [ H : estep _ _ _ _ _ _ |- _ ] => inversion H end.

Global Hint Constructors estep jstep cstep.

Ltac is_jmp_false k :=
  let k' := fresh "k'" in
  let ks' := fresh "ks'" in
  let IHks' := fresh "IHks'" in
  induction k as [|k' ks' IHks']=>//;
  simpl; induction k'; simpl; try (rewrite IHks'); auto;
  rewrite existsb_app; simpl; rewrite IHks'; simpl;
  by apply orb_true_r.

Lemma is_jmp_ret k v: is_jmp (fill_ectxs (Erete (Evalue v)) k) = true.
Proof. is_jmp_false k. Qed.

Lemma is_jmp_call k' t f es: is_jmp (fill_ectxs (Ecall t f es) k') = true.
Proof. is_jmp_false k'. Qed.

Lemma is_jmp_while k' c e: is_jmp (fill_ectxs (Ewhile c e) k') = true.
Proof. is_jmp_false k'. Qed.

Lemma is_jmp_break k': is_jmp (fill_ectxs Ebreak k') = true.
Proof. is_jmp_false k'. Qed.

Lemma is_jmp_continue k': is_jmp (fill_ectxs Econtinue k') = true.
Proof. is_jmp_false k'. Qed.

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
    end; auto.
  - by rewrite is_jmp_ret in Hnj.
  - by rewrite is_jmp_call in Hnj.
Qed.

Lemma is_jmp_wstep_false {e e'} k {ks ks'}:
  to_val e = None →
  is_jmp e = false →
  wstep (fill_ectxs e k) ks e' ks' → false.
Proof.
  intros Hnv Hnj.
  inversion 1; subst;
    match goal with
    | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _ ] =>
      symmetry in H;
      apply unfill_segment in H=>//;
      destruct H as [? [? ?]]; subst
    end; auto.
  - by rewrite is_jmp_while in Hnj.
  - by rewrite is_jmp_break in Hnj.
  - by rewrite is_jmp_continue in Hnj.
Qed.

Ltac inversion_jstep_as Heq :=
  match goal with
  | [ Hjs: jstep _ _ _ _ _ |- _ ] =>
    inversion Hjs as [?|?]; subst;
    match goal with
    | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _ ] => rename H into Heq
    | _ => idtac
    end
  end.

Ltac inversion_wstep_as Heq :=
  match goal with
  | [ Hws: wstep _ _ _ _ |- _ ] =>
    inversion Hws as [?|?|?]; subst;
    match goal with
    | [ H : fill_ectxs _ _ = fill_ectxs _ _ |- _ ] => rename H into Heq
    | _ => idtac
    end
  end.

Lemma cstep_not_val {e σ s e' σ' s' efs}:
  cstep e σ s e' σ' s' efs → to_val e = None.
Proof.
  inversion 1; subst=>//.
  - by eapply estep_not_val.
  - inversion_jstep_as Heq; by apply fill_ectxs_not_val.
  - inversion_wstep_as Heq; by apply fill_ectxs_not_val.
Qed.

Lemma CSbind' e e' σ σ' s s' efs k kes:
  is_jmp e = false →
  cstep e s σ e' s' σ' efs →
  cstep (fill_ectxs e (k::kes)) s σ (fill_ectxs e' (k::kes)) s' σ' efs.
Proof.
  intros Hnj Hcs. inversion Hcs; subst.
  - apply CSestep. apply ESbind=>//.
  - exfalso. move: (cstep_not_val Hcs) => Hn.
    apply (is_jmp_jstep_false [] Hn Hnj H).
  - exfalso. move: (cstep_not_val Hcs) => Hn.
    apply (is_jmp_wstep_false [] Hn Hnj H).
Qed.

Lemma CSbind:
    ∀ e e' σ σ' s s' kes efs,
      is_jmp e = false →
      cstep e s σ e' s' σ' efs →
      cstep (fill_ectxs e kes) s σ (fill_ectxs e' kes) s' σ' efs.
Proof. induction kes=>//. intros. apply CSbind'=>//. Qed.

Instance state_inhabited: Inhabited state := populate (State ∅ ∅).

Lemma not_jmp_preserves k e e' σ σ' s s' efs:
  to_val e = None →
  is_jmp e = false →
  cstep (fill_ectxs e k) s σ e' s' σ' efs →
  s = s' ∧ s_text σ = s_text σ' ∧
  estep (s_text σ) (fill_ectxs e k) (s_heap σ) e' (s_heap σ') efs.
Proof.
  intros Hnv Hnj Hcs. inversion Hcs; subst=>//.
  - exfalso. eapply (is_jmp_jstep_false k)=>//.
  - exfalso. eapply (is_jmp_wstep_false k)=>//.
Qed.

Lemma fill_step_inv e1' σ1 e2 σ2 s1 s2 K efs:
  wellformed e1' →
  is_jmp e1' = false →
  cstep (fill_ectxs e1' K) s1 σ1 e2 s2 σ2 efs →
  ∃ e2', e2 = fill_ectxs e2' K ∧ cstep e1'  s1 σ1 e2' s2 σ2 efs ∧ s1 = s2.
Proof.
  intros Hnv Hnj.
  inversion 1; subst.
  - eapply fill_estep_inv in H0=>//; last by apply wf_not_val.
    destruct H0 as (e2'&?&?).
    exists e2'. split; [| split ]; auto.
  - inversion_jstep_as Heq;
    eapply cont_incl in Heq=>//;
    try destruct Heq as (?&?); subst; auto.
    + by rewrite is_jmp_ret in Hnj.
    + by rewrite is_jmp_call in Hnj.
  - inversion_wstep_as Heq;
    eapply cont_incl in Heq=>//;
    try destruct Heq as (?&?); subst; auto.
    + by rewrite is_jmp_while in Hnj.
    + by rewrite is_jmp_break in Hnj.
    + by rewrite is_jmp_continue in Hnj.
Qed.

Lemma instantiate_let_preserves_not_jmp x xv xt e e':
  instantiate_let x xv xt e = Some e' →
  is_jmp e = false →
  is_jmp e' = false.
Admitted. (* Apparent but hard for now. Documented *)

Lemma estep_preserves_not_jmp' σ1 σ2:
  let P e1 :=
      (∀ e2 G efs, is_jmp e1 = false → estep G e1 σ1 e2 σ2 efs → is_jmp e2 = false)
  in ∀ e1, wellformed e1 → P e1.
Proof.
  intros P. apply (not_val_ind'' P).
  - unfold P. intros e Henf e2 G efs Hjn Hes.
    inversion Hes=>//; subst; simpl in Hes=>//; simpl in Hjn.
    + by eapply instantiate_let_preserves_not_jmp.
    + solve_is_jmp_false.
    + solve_is_jmp_false.
    + simpl in Hjn. exfalso.
      simpl in Henf. escape_false.
  - unfold P. intros e ks Henf Hind e2 G efs Hjn Hes.
    inversion_cstep Henf ltac:(inversion Hjn); simplify_eq
    ; try by (simpl; rewrite -H1 in Hjn; inversion Hjn; solve_is_jmp_false).
    + simplify_eq. eapply instantiate_let_preserves_not_jmp=>//.
      rewrite -H in Hjn. by simpl in Hjn.
    + assert (is_jmp e' = false).
      { eapply (Hind K')=>//. rewrite app_length. simpl. omega. }
      rewrite -fill_app in Hjn.
      eapply is_jmp_out in Hjn=>//.
Qed.

Lemma estep_preserves_not_jmp'' e σ1 e2' σ2 G efs:
  to_val e = None → is_jmp e = false →
  estep G e σ1 e2' σ2 efs → is_jmp e2' = false.
Proof.
  intros H ??.
  move:(wellformed_estep H1)=>Hwf.
  move: (estep_preserves_not_jmp' σ1 σ2 e Hwf e2' G efs) => /= H'.
  auto.
Qed.

Lemma estep_preserves_not_jmp e σ1 e2' σ2 G efs:
  is_jmp e = false → estep G e σ1 e2' σ2 efs → is_jmp e2' = false.
Proof.
  destruct (to_val e) eqn:Heq.
  - apply of_to_val in Heq. subst. inversion 2.
    subst. exfalso. apply estep_not_val in H0=>//.
  - by apply estep_preserves_not_jmp''.
Qed.

Lemma cstep_preserves_not_jmp e s1 σ1 e2' s2 σ2 efs:
  is_jmp e = false → cstep e s1 σ1 e2' s2 σ2 efs → is_jmp e2' = false.
Proof.
  inversion 2; subst.
  - inversion_estep; subst=>//; try by (simpl in *; solve_is_jmp_false).
    + by eapply instantiate_let_preserves_not_jmp.
    + eapply estep_preserves_not_jmp; first apply H; done.
  - exfalso. move:(cstep_not_val H0)=>Hn.
    by eapply (is_jmp_jstep_false []).
  - exfalso. move:(cstep_not_val H0)=>Hn.
    by eapply (is_jmp_wstep_false []).
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
      intros Hv1 Hv2; subst; destruct p; simpl in Hv1, Hv2;
        try by (destruct_ands; inversion_eq).
  - rewrite Byte.repr_unsigned in Hv2, Hv1.
    destruct_ands.
    inversion_eq.
    by rewrite Byte.repr_unsigned.
  - destruct_ands.
    admit.
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

Lemma cstep_not_val' e s σ e' s' σ' efs:
  cstep e s σ e' s' σ' efs → to_val e = None.
Proof. by eapply cstep_not_val. Qed.

Definition clang_lang :=
  Language expr val local_state state Evalue to_val
           [] cstep to_of_val of_to_val cstep_not_val'.

Ltac absurd_jstep' :=
  match goal with
  | [ HF: fill_ectxs _ _ = ?E |- _ ] =>
    replace E with (fill_ectxs E []) in HF=>//; apply cont_inj in HF=>//;
      by destruct HF; auto
  end.

Ltac absurd_jstep Hjs :=
  inversion Hjs; simplify_eq; last absurd_jstep';
  match goal with
  | [ HF: fill_ectxs _ _ = _ |- _ ] =>
      by apply weak_cont_inj in HF; eauto; destruct_ands
  end.

Ltac atomic_step H :=
  inversion H; subst;
  [ match goal with
    | [ HE: estep _ _ _ _ _ _ |- _ ] =>
      inversion HE; subst;
      [ idtac | exfalso; by escape_false ]
    end
  | match goal with
    | [ HJ : jstep _ _ _ _ _ |- _ ] => absurd_jstep HJ
    end
  | match goal with
    | [ HW : wstep _ _ _ _ |- _ ] => absurd_jstep HW
    end
  ].

Definition clang_atomic (e: expr) :=
  match e with
  | ECAS t e1 e2 e3 => bool_decide (is_loc e1 ∧ is_val e2 ∧ is_val e3)
  | Ederef_typed t e => bool_decide (is_loc e)
  | Ealloc t e => bool_decide (is_val e)
  | Eassign e1 e2 => bool_decide (is_loc e1 ∧ is_val e2)
  | _ => false
  end.

Ltac inversion_cstep_as Hes Hjs Hws :=
  match goal with
    | [ Hcs : cstep _ _ _ _ _ _ _ |- _ ] =>
      inversion Hcs as [????????Hes|???????Hjs|??????Hws]; subst
  end.

Lemma atomic_enf e:
  clang_atomic e → language.atomic (e: language.expr clang_lang).
Proof.
  - intros ??????? Hcs. apply language.val_irreducible. simpl in *.
    destruct e=>//.
    + destruct e1=>//. destruct v=>//.
      destruct e2=>//. destruct e3=>//.
      inversion_cstep_as Hes Hjs Hws.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
      { absurd_jstep Hws. }
    + destruct e=>//.
      inversion_cstep_as Hes Hjs Hws.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
      { absurd_jstep Hws. }
    + destruct e=>//. inversion_cstep_as Hes Hjs Hws.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
      { absurd_jstep Hws. }
    + destruct e1=>//. destruct v=>//. destruct e2=>//.
      inversion_cstep_as Hes Hjs Hws.
      { inversion Hes; subst=>//;
        ((exfalso; by escape_false) || (simpl; by eauto)). }
      { absurd_jstep Hjs. }
      { absurd_jstep Hws. }
Qed.

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

Definition Edecl (t: type) (x: ident) e : expr :=
  Elet t x (Ealloc t (Evalue (default_val t))) e.
