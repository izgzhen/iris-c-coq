From iris_c.clang Require Import logic notations tactics.
From iris_c.clang.lib Require Import lock.
From iris_c.lib Require Import int.

Section test.
  Context `{clangG Σ}.

  Definition x : ident := 1.
  Definition r : ident := 2.
  Definition l : ident.
  
  Definition add: expr :=
    lock l
    r <- vtrue.

  Lemma add_spec:
    r ↦ 