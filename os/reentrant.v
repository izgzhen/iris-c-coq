(* Reentrant Lock *)

Require Import logic.

(* TODO: Implementation *)
(* Class reentG Σ := ReentG { *)
(*   reent_G :> inG Σ (authR (gset_disjUR nat)) *)
(* }. *)

(* Interface *)
  
Structure reent_lock Σ `{!clangG Σ} := ReentLock {
  (* -- operations -- *)
  newlock_f : function;
  acquire_f : function;
  release_f : function;
  newlock : ident;
  acquire : ident;
  release : ident;
  (* -- predicates -- *)
  (* name is used to associate locked with is_lock *)
  name : Type;
  is_lock (N: namespace) (γ: name) (lock: val) (R: iProp Σ) : iProp Σ;
  locked (γ: name) (depth: nat) : iProp Σ;
  (* -- general properties -- *)
  is_lock_ne N γ lk n: Proper (dist n ==> dist n) (is_lock N γ lk);
  is_lock_persistent N γ lk R : PersistentP (is_lock N γ lk R);
  locked_timeless γ d: TimelessP (locked γ d);
  locked_exclusive γ d1 d2: locked γ d1 -∗ locked γ d2 -∗ False;
  (* -- operation specs -- *)
  newlock_spec N (R : iProp Σ) Φ Φret:
    R ∗ (∀ lk γ, is_lock N γ lk R -∗ Φ lk)
    ⊢ WP (curs (Scall newlock []), knil) {{ Φ; Φret }};
  acquire0_spec N γ lk R Φ Φret:
    is_lock N γ lk R ∗ (locked γ 0 -∗ R -∗ Φ)
    ⊢ WP (curs (Scall acquire [Evalue lk]), knil) {{ _, Φ; Φret }};
  acquiren_spec γ N R n lk Φ Φret:
    is_lock N γ lk R ∗ locked γ n ∗ (locked γ (n + 1) -∗ Φ)
    ⊢ WP (curs (Scall acquire [Evalue lk]), knil) {{ _, Φ; Φret }};
  release0_spec N γ lk R Φ Φret:
    is_lock N γ lk R ∗ locked γ 0 ∗ R ∗ (True -∗ Φ)
    ⊢ WP (curs (Scall release [Evalue lk]), knil) {{ _, Φ; Φret }};
  releasen_spec N γ n lk R Φ Φret:
    is_lock N γ lk R ∗ locked γ (S n) ∗ (locked γ n -∗ Φ)
    ⊢ WP (curs (Scall release [Evalue lk]), knil) {{ _, Φ; Φret }}
}.

Arguments newlock {_ _} _.
Arguments acquire {_ _} _.
Arguments release {_ _} _.
Arguments is_lock {_ _} _ _ _ _ _.
Arguments locked {_ _} _ _ _.

Existing Instances is_lock_ne is_lock_persistent locked_timeless.

Instance is_lock_proper Σ `{!clangG Σ} (L: reent_lock Σ) N lk R:
  Proper ((≡) ==> (≡)) (is_lock L N lk R) := ne_proper _.

