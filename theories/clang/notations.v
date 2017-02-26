From iris_os.clang Require Import lang.
Set Default Proof Using "Type".

Coercion Vint8 : int8 >-> val.
Coercion Vint32 : int32 >-> val.
Coercion Vptr : addr >-> val.

(* Coercion App : expr >-> Funclass. *)
Coercion of_val : val >-> expr.

Coercion Evar : ident >-> expr.

Notation "'void'" := Vvoid.
Notation "'null'" := Vnull.
Notation "'true'" := vtrue : expr_scope.
Notation "'false'" := vfalse : expr_scope.
Notation "# v" := (Evalue v) (at level 8) : expr_scope.
Notation "! e" := (Ederef e%E) (at level 9, right associativity) : expr_scope.
Notation "'fst' e" := (Efst e%E) (at level 9, right associativity) : expr_scope.
Notation "'snd' e" := (Esnd e%E) (at level 9, right associativity) : expr_scope.
Notation "! e" := (Ederef e%E) (at level 9, right associativity) : expr_scope.
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
Notation "e 'as' t" := (Ecast e%E t)
  (at level 50, left associativity) : expr_scope.

Notation "e1 <- e2" := (Sassign e1%E e2%E) (at level 80) : stmts_scope.
Notation "'if' ( e ) { s1 } 'else' { s2 }" := (Sif e%E s1%S s2%S)
  (at level 200, e, s1, s2 at level 200) : stmts_scope.
Notation "'while' ( e ) <{ s }>" := (Swhile e%E s%S)
  (at level 200, e, s at level 200) : stmts_scope.
Notation "s1 ;; s2" := (Sseq s1%S s2%S)
  (at level 100, s2 at level 200, format "s1  ;;  s2") : stmts_scope.
Notation "'ret'" := Sret (at level 80): stmts_scope.
Notation "'rete' e" := (Srete e%E) (at level 80): stmts_scope.
Notation "f < e1 , e2 , .. , en >" := (Scall f (cons e1%E (cons e2%E .. (cons en%E nil) .. )))
  (at level 80) : stmts_scope.
Notation "'skip'" := (Sskip) (at level 200) : stmts_scope.

Notation "'cli'" := (Sprim Pcli) (at level 80) : stmts_scope.
Notation "'sti'" := (Sprim Psti) (at level 80) : stmts_scope.
