(** Language definition **)

From iris.base_logic Require Export gen_heap big_op.
From iris.algebra Require Import gmap.
From iris_os.lib Require Export smap prelude.
From iris.program_logic Require Export language.
From iris_os.clang Require Export memory types.

Open Scope Z_scope.

Inductive bop :=
| oplus
| ominus
| oequals
| oneq
| oless.

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
| Eseq (s1 s2: expr)
| Eprim (p: prim).

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
    | EKseq s => Eseq e s
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
    | byte::bs' => let '(b, o) := l in σ !! l = Some byte ∧ readbytes (b, o + 1)%nat bs' σ
    | _ => True
  end.

Lemma readbytes_segment σ bs': ∀ bs l,
  readbytes l (bs ++ bs') σ → readbytes l bs σ.
Proof.
  induction bs=>//.
  intros. destruct l. simpl. simpl in H.
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
  - intros. destruct l. simpl. simpl in H.
    destruct H.
    specialize (IHbs _ H0).
    simpl in IHbs.
    replace (n + S (length bs))%nat with (n + 1 + length bs)%nat=>//.
    omega.
Qed.

Fixpoint storebytes l bs (σ: heap) :=
  match bs with
    | byte::bs' => let '(b, o) := l in <[ l := byte ]> (storebytes (b, o + 1)%nat bs' σ)
    | _ => σ
  end.

Definition alloc_heap (l: addr) (v: val) (σ: heap) : heap := storebytes l (encode_val v) σ.

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

Lemma fill_ectxs_not_val Kes: ∀ e, to_val e = None → to_val (fill_ectxs e Kes) = None.
Proof. induction Kes; first by inversion 1.
       intros. simpl. apply fill_ectx_not_val.
Qed.

Fixpoint params_match (params: decls) (vs: list val) :=
  match params, vs with
    | (_, t)::params, v::vs => typeof v t ∧ params_match params vs
    | [], [] => True
    | _, _ => False
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
    | Eprim p => Some e
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
    | Eprim _ => Some e
  end.

Fixpoint add_params_to_env (e: env) (params: list (ident * type)) ls : env :=
  match params, ls with
    | (x, t)::ps, l::ls' => add_params_to_env (Env (sset x (t, l) (lenv e)) (fenv e)) ps ls'
    | _, _ => e
  end.

Definition instantiate_f_body (ev: env) (s: expr) : option expr :=
  (resolve_rhs ev s ≫= resolve_lhs ev).

Fixpoint is_jmp (e: expr) :=
  match e with
    | Ecall _ es => true
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
    | _ => false
  end.

Lemma is_jmp_rec' e K:
  is_jmp (fill_expr e K) = false → is_jmp e = false.
Proof.
  induction K=>//; simpl; intros.
  - destruct (is_jmp re); destruct (is_jmp e)=>//.
  - destruct (is_jmp rhs); destruct (is_jmp e)=>//.
  - destruct (is_jmp s1); destruct (is_jmp s2); destruct (is_jmp e)=>//.
  - destruct (is_jmp s); destruct (is_jmp e); destruct (is_jmp cond)=>//.
  - destruct (is_jmp s); destruct (is_jmp e)=>//.
Qed.

Lemma is_jmp_rec e ks:
  is_jmp (fill_ectxs e ks) = false → is_jmp e = false.
Proof.
  induction ks=>//.
  simpl; intros.
  apply is_jmp_rec' in H.
  auto.
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
| ESbind':
    ∀ e e' σ σ' k kes,
      is_jmp e = false →
      estep e σ e' σ' →
      estep (fill_ectxs e (k::kes)) σ (fill_ectxs e' (k::kes)) σ'
.

Lemma ESbind:
    ∀ kes e e' σ σ',
      is_jmp e = false →
      estep e σ e' σ' →
      estep (fill_ectxs e kes) σ (fill_ectxs e' kes) σ'.
Proof. induction kes=>//. intros. apply ESbind'=>//. Qed.

Lemma estep_not_val e σ e' σ':
  estep e σ e' σ' → to_val e = None.
Proof. induction 1=>//. by apply fill_ectxs_not_val. Qed.

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
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e1 (EKif e2 e3 :: ks)
      end
    | Ewhile c e s =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKwhile c s :: ks)
      end
    | Erete e =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e (EKrete :: ks)
      end
    | Eseq e1 e2 =>
      match e with
        | Evalue v => Some (ks, e)
        | _ => unfill_expr e1 (EKseq e2 :: ks)
      end
    | _ => None
  end.

Definition is_val e := is_some (to_val e).

Lemma to_val_is_val e:
  to_val e = None ↔ is_val e = false.
Proof. induction e; crush. Qed.

Lemma forall_is_val ls:
  forallb is_val (map (λ l : addr, Evalue (Vptr l)) ls) = true.
Proof. by induction ls=>//. Qed.

Definition is_loc e :=
  match to_val e with
    | Some (Vptr _) => true
    | _ => false
  end.

Definition enf (e: expr) :=
  match e with
    | Ecall _ es => forallb is_val es
    | Erete e => is_val e
    | Ebinop _ e1 e2 => is_val e1 && is_val e2
    | Ederef e => is_val e
    | Ederef_typed _ e => is_val e
    | Eaddrof e => is_val e
    | Efst e => is_val e
    | Esnd e => is_val e
    | Ealloc _ e => is_val e
    | Eassign e1 e2 => is_loc e1 && is_val e2
    | Eif e1 e2 e3 => is_val e1
    | Eseq e1 e2 => is_val e1
    | Ewhile _ e _ => is_val e
    | _ => false
  end.

Lemma enf_not_val e: enf e = true → to_val e = None.
Proof. induction e; crush. Qed.

Definition unfill e kes := unfill_expr (fill_ectxs e kes) [] = Some (kes, e).

Axiom cont_uninj: ∀ kes e, enf e = true → unfill e kes.  

Lemma cont_inj {e e' kes kes'}:
  enf e = true → enf e' = true →
  fill_ectxs e kes = fill_ectxs e' kes' → e = e' ∧ kes = kes'.
Proof.
  intros. apply (cont_uninj kes) in H.
  apply (cont_uninj kes') in H0.
  unfold unfill in H0, H.
  rewrite H1 in H. by simplify_eq.
Qed.


Lemma fill_not_enf e k:
  is_val e = false → enf (fill_expr e k) = false.
Proof. induction k=>//.
       - intros H. simpl. rewrite H. done.
       - intros H. simpl. rewrite forallb_app.
         replace (e::args) with ([e] ++ args); last done.
         rewrite forallb_app. simpl. rewrite H.
         by rewrite andb_false_r.
       - intros H. simpl. induction e; crush.
Qed.

Lemma escape_false {e a e' a2 kes k0 e''}:
  estep e a e' a2 →
  fill_expr (fill_ectxs e kes) k0 = e'' → enf e'' = true → False.
Proof.
  intros. assert (enf e'' = false) as Hfalse; last by rewrite Hfalse in H1.
  rewrite -H0. apply fill_not_enf.
  apply to_val_is_val.
  apply fill_ectxs_not_val. eapply estep_not_val. done.
Qed.

Ltac gen_eq H E1 E2 KS :=
  replace E1 with (fill_ectxs E1 []) in H; last done;
  assert (E1 = E2 ∧ [] = KS) as [? ?];
  [ apply cont_inj=>// | subst; clear H ].

(* Difficulty: super hard *)
Lemma focus_estep_inv {e1 σ1 e2 σ2}:
  estep e1 σ1 e2 σ2 →
  ∃ e1' e2' K, enf e1' = true ∧ e1 = fill_ectxs e1' K ∧ estep e1' σ1 e2' σ2 ∧ e2 = fill_ectxs e2' K.
Admitted.

(* Difficulty: super hard *)
Lemma fill_estep_false {e kes e' σ σ'}:
  is_jmp e = true →
  estep (fill_ectxs e kes) σ e' σ' → False.
Admitted.

Lemma fill_app e K K': fill_ectxs (fill_ectxs e K) K' = fill_ectxs e (K' ++ K).
Proof. induction K'=>//. simpl. by rewrite IHK'. Qed.

Axiom not_val_ind:
  ∀ P: expr → Prop,
    (∀ e, enf e = true → P e) →
    (∀ e ks, to_val e = None → P e → P (fill_ectxs e ks)) →
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
  - unfold P. intros.
    eapply focus_estep_inv in H1.
    destruct H1 as (?&?&?&?&?&?&?).
    eapply cont_inj in H2=>//.
    destruct H2. subst. eauto.
  - unfold P. intros.
    rewrite fill_app in H2.
    apply H0 in H2; last by eapply is_jmp_rec.
    destruct H2 as (?&?&?).
    exists (fill_ectxs x ks).
    split. apply ESbind=>//.
    by eapply is_jmp_rec.
    by rewrite fill_app.
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
        enf e = true →
        fill_ectxs e kes = fill_ectxs e' kes' →
        ∃ kes'', e' = fill_ectxs e kes'')
  in ∀ e', to_val e' = None → P e'.
Proof.
  intros P. apply (not_val_ind P).
  - unfold P. intros.
    apply cont_inj in H1=>//.
    destruct H1. subst.
    by exists [].
  - unfold P. intros.
    rewrite fill_app in H2.
    apply H0 in H2=>//.
    destruct H2.
    subst. rewrite fill_app. eauto.
Qed.

Lemma cont_incl {e' kes kes' e}:
  enf e = true →
  to_val e' = None →
  fill_ectxs e kes = fill_ectxs e' kes' →
  ∃ kes'', e' = fill_ectxs e kes''.
Proof. move: cont_incl' => /= H. intros. by eapply H. Qed.

Inductive jstep: text → expr → stack → expr → stack → Prop :=
| JSrete:
    ∀ t v k k' ks,
      unfill (Erete (Evalue v)) k' →
      jstep t (fill_ectxs (Erete (Evalue v)) k') (k::ks) (fill_ectxs (Evalue v) k) ks
| JScall:
    ∀ t es ls retty params f_body f_body' f k ks,
      es = map (fun l => Evalue (Vptr l)) ls →
      t !! f = Some (Function retty params f_body) →
      instantiate_f_body (add_params_to_env (Env [] []) params ls) f_body = Some f_body' →
      jstep t (fill_ectxs (Ecall f es) k) ks f_body' (k::ks).

Bind Scope val_scope with val.
Delimit Scope val_scope with V.
Bind Scope expr_scope with expr.
Delimit Scope expr_scope with E.
Bind Scope prim_scope with prim.
Delimit Scope prim_scope with prim.

Inductive cstep: expr → state → expr → state → Prop :=
| CSestep:
    ∀ s t e h e' h', estep e h e' h' → cstep e (State h t s) e' (State h' t s)
| CSjstep:
    ∀ e e' h t s s' , jstep t e s e' s' → cstep e (State h t s) e' (State h t s').

Lemma is_jmp_ret k' v: is_jmp (fill_ectxs (Erete (Evalue v)) k') = true.
Proof. induction k'=>//. simpl; induction a; simpl; try (rewrite IHk'); auto. Qed.

Lemma is_jmp_call k' f es: is_jmp (fill_ectxs (Ecall f es) k') = true.
Proof. induction k'=>//. simpl; induction a; simpl; try (rewrite IHk'); auto. Qed.

Lemma is_jmp_jstep_false {e e' σ ks ks'}:
  is_jmp e = false →
  jstep σ e ks e' ks' → false.
Proof.
  inversion 2; subst.
  - by rewrite is_jmp_ret in H.
  - by rewrite is_jmp_call in H.
Qed.
  
Lemma CSbind':
    ∀ e e' σ σ' k kes,
      is_jmp e = false →
      cstep e σ e' σ' →
      cstep (fill_ectxs e (k::kes)) σ (fill_ectxs e' (k::kes)) σ'.
Proof.
  intros. inversion H0; subst.
  - apply CSestep. apply ESbind=>//.
  - exfalso. by eapply is_jmp_jstep_false.
Qed.

Lemma CSbind:
    ∀ e e' σ σ' kes,
      is_jmp e = false →
      cstep e σ e' σ' →
      cstep (fill_ectxs e kes) σ (fill_ectxs e' kes) σ'.
Proof. induction kes=>//. intros. apply CSbind'=>//. Qed.

Instance state_inhabited: Inhabited state := populate (State ∅ ∅ []).

Lemma not_jmp_preserves_stack e e' σ σ':
  is_jmp e = false → cstep e σ e' σ' → s_stack σ = s_stack σ'.
Proof.
  intros. inversion H0; subst=>//.
  exfalso. by eapply is_jmp_jstep_false.
Qed.

Lemma fill_step_inv e1' σ1 e2 σ2 K:
  to_val e1' = None →
  is_jmp e1' = false →
  cstep (fill_ectxs e1' K) σ1 e2 σ2 →
  ∃ e2', e2 = fill_ectxs e2' K ∧ cstep e1' σ1 e2' σ2 ∧ s_stack σ1 = s_stack σ2.
Proof.
  inversion 3; subst.
  - eapply fill_estep_inv in H2=>//.
    destruct H2 as (?&?&?).
    exists x. split; [done | split; [ by constructor | done ] ].
  - inversion H2; subst.
    + eapply cont_incl in H3=>//.
      destruct H3 as (?&?); subst.
      by rewrite is_jmp_ret in H0.
    + eapply cont_incl in H3=>//.
      destruct H3 as (?&?); subst.
      by rewrite is_jmp_call in H0. apply forall_is_val.
Qed.

Lemma estep_preserves_not_jmp e σ1 e2' σ2:
  is_jmp e = false → estep e σ1 e2' σ2 → is_jmp e2' = false.
Admitted.

Lemma cstep_preserves_not_jmp e σ1 e2' σ2:
  is_jmp e = false → cstep e σ1 e2' σ2 → is_jmp e2' = false.
Proof.
  inversion 2; subst.
  - inversion H1; subst=>//.
    + simpl in H. simpl.
      destruct (is_jmp cond); destruct (is_jmp s0)=>//.
    + by eapply estep_preserves_not_jmp.
  - exfalso. by eapply is_jmp_jstep_false.
Qed.

Lemma same_type_encode_inj σ:
  ∀ t v v' p,
    typeof v t → typeof v' t →
    readbytes p (encode_val v) σ →
    readbytes p (encode_val v') σ →
    v = v'.
Proof.
  induction t.
  - intros. inversion H. inversion H0. done.
  - intros. inversion H. inversion H0. done.
  - intros. inversion H. inversion H0.
    subst. destruct p. simpl in H1, H2.
    rewrite Byte.repr_unsigned in H2.
    rewrite Byte.repr_unsigned in H1.
    destruct H2. destruct H1. rewrite H2 in H1.
    by inversion H1.
  - intros.
    inversion H. inversion H0.
    subst. destruct p. simpl in H1, H2.
    destruct H2 as (?&?&?&?&?).
    destruct H1 as (?&?&?&?&?).
    rewrite H2 in H1. rewrite H3 in H7.
    rewrite H4 in H8. rewrite H5 in H9.
    admit. (* Hairy arithmetic -- should be right *)
  - intros. inversion H; inversion H0; subst; destruct p; simpl in H1, H2=>//.
    + destruct H1. destruct H2.
      by rewrite H2 in H1.
    + destruct H1. destruct H2.
      by rewrite H2 in H1.
    + destruct H1. destruct H2.
      rewrite H2 in H1. by inversion H1.
  - intros.
    inversion H. inversion H0. subst.
    f_equal.
    + eapply IHt1=>//.
      simpl in H1. by eapply readbytes_segment.
      simpl in H2. by eapply readbytes_segment.
    + eapply IHt2=>//.
      * simpl in H1. by eapply readbytes_segment_2.
      * simpl in H2.
        replace (length (encode_val v1)) with
        (length (encode_val v0)).
        by eapply readbytes_segment_2.
        { rewrite -(typeof_preserves_size v0 t1)=>//.
          rewrite -(typeof_preserves_size v1 t1)=>//. }
Admitted.

Lemma estep_call_false f ls σ1 e' σ2:
  estep (Ecall f (map (λ l, Evalue (Vptr l)) ls)) σ1 e' σ2 → False.
Proof.
  intros. inversion H. subst. eapply (escape_false H2)=>//.
  apply forall_is_val.
Qed.

Definition step e σ e' σ' (efs: list expr) := cstep e σ e' σ' ∧ efs = [].

Lemma step_not_val e σ e' σ' efs:
  step e σ e' σ' efs → to_val e = None.
Proof.
  destruct 1. inversion H; subst.
  - by eapply estep_not_val.
  - inversion H1; by apply fill_ectxs_not_val.
Qed.

Definition clang_lang :=
  Language expr val state Evalue to_val step to_of_val of_to_val step_not_val.
