From iris_c.clang Require Import lang.
Set Default Proof Using "Type".

Coercion Vint8 : int8 >-> val.
Coercion Vint32 : int32 >-> val.
Coercion Vptr : addr >-> val.
Coercion Evalue : val >-> expr.
Coercion Evar : ident >-> expr.

Notation "'void'" := Vvoid.
Notation "'null'" := Vnull.
Notation "# v" := (Evalue v) (at level 8) : expr_scope.
Notation "!? e" := (Ederef e%E) (at level 9, right associativity) : expr_scope.
Notation "! e @ t" := (Ederef_typed t e%E) (at level 9, right associativity) : expr_scope.
Notation "'fst' e" := (Efst e%E) (at level 9, right associativity) : expr_scope.
Notation "'snd' e" := (Esnd e%E) (at level 9, right associativity) : expr_scope.
Notation "& e" := (Eaddrof e%E)
  (at level 30, right associativity) : expr_scope.
Notation "e1 + e2" := (Ebinop oplus e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 - e2" := (Ebinop ominus e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 == e2" := (Ebinop oequals e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 != e2" := (Ebinop oneq e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "e1 :<: e2" := (Ebinop oless e1%E e2%E)
  (at level 50, left associativity) : expr_scope.
Notation "f # t <$ e1 , e2 , .. , en $>" := (Ecall_typed t f (cons e1%E (cons e2%E .. (cons en%E nil) .. )))
  (at level 50) : expr_scope.

Notation "e1 <- e2" := (Eassign e1%E e2%E) (at level 80) : expr_scope.
Notation "'if:' ( e ) then: { s1 } 'else:' { s2 }" := (Eif e%E s1%E s2%E)
  (at level 200, e, s1, s2 at level 200) : expr_scope.
Notation "'while' [ c ] ( e ) <{ s }>" := (Ewhile c%E e%E s%E)
  (at level 200, c, e, s at level 200) : expr_scope.
Notation "s1 ;; s2" := (Eseq s1%E s2%E)
  (at level 100, s2 at level 200, format "s1  ;;  s2") : expr_scope.
Notation "'return:' e" := (Erete e%E) (at level 80): expr_scope.
Notation "'let:' x ::: t := e1 'in' e2" := (Elet_typed t x e1%E e2%E)
  (at level 102, x, t at level 1, e1, e2 at level 200) : expr_scope.