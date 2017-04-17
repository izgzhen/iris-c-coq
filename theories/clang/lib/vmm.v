From iris_c.clang Require Import logic notations.
Require Import iris_c.clang.lib.page_table.

Section vmm.
  Context `{clangG Σ} {pt: page_table Σ}.

  Definition mem_init (n: nat) (x: addr) (y: addr) : expr :=
    x <- Int.repr 0 ;;
    while [ !x@Tint32 :<: Int.repr n ] ( !x@Tint32 :<: Int.repr n ) <{
      y <- Ealloc (Tprod Tint8 Tvoid) (Vpair vfalse Vvoid) ;;
      insert_pt pt <$ !x@Tint32 , Evalue (Vptr y) $>
    }>.

  Fixpoint allocated m (n: nat) : iProp Σ :=
    match m !! Int.repr n with
      | None => False%I
      | Some p =>
        (p ↦ (Vpair vfalse Vvoid) @ (Tprod Tint8 Tvoid) ∗
           match n with
             | O => True
             | S n' => allocated m n'
        end)%I
      end.

  Lemma mem_init_spec n x y Φ:
    is_page_table pt ∅ ∗ (∀ m, allocated m (n - 1) -∗ is_page_table pt m -∗ Φ Vvoid)
    ⊢ WP mem_init n x y {{ Φ }}.
  Admitted.

End vmm.
