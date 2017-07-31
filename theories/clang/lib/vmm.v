From iris_c.clang Require Import logic notations.
Require Import iris_c.clang.lib.page_table.
Require Import iris_c.lib.int.

Section vmm.
  Context `{G: clangG Σ} {pt: @page_table Σ G}.

  Definition mem_init (n: nat) (x: addr) (y: addr) : expr :=
    x <- 0 ;;
    while: ( !x@Tint8 :<: n ) (
      y <- Ealloc (Tprod Tint8 Tvoid) (Vpair vfalse Vvoid) ;;
      Ecall Tvoid (insert_pt pt) (Epair (!x@Tint8) (Evalue (Vpair (Vptr y) Vvoid)))
    ).

  Fixpoint allocated (m: gmap int8 addr) (n: nat) : iProp Σ :=
    match m !! Byte.repr n with
      | None => False%I
      | Some p =>
        (p ↦ (Vpair vfalse Vvoid) @ (Tprod Tint8 Tvoid) ∗
           match n with
             | O => True
             | S n' => allocated m n'
        end)%I
      end.

End vmm.
