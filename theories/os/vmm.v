From iris_os.clang Require Import logic notations.
Require Import iris_os.os.page_table.

Section vmm.
  Context `{clangG Σ} {pt: page_table Σ}.

  Definition mem_init (n: int32) (x: addr) (y: addr) : expr :=
    x <- Int.repr 0 ;;
    while [ x :<: n ] ( x :<: n ) <{
      y <- Ealloc (Tprod Tint8 Tvoid) (Vpair vfalse Vvoid) ;;
      insert_pt pt <$ Evalue (Vptr x) , Evalue (Vptr y) $>
    }>.
End vmm.
