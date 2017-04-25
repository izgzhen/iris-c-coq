(* Virtual Memory Model *)

Require Import iris_c.clang.logic.

Definition option_addr_to_val (opt_a: option addr) : val :=
  match opt_a with
    | Some a => Vptr a
    | None => Vnull
  end.

Structure page_table Σ `{!clangG Σ} :=  {
  (* -- operations -- *)
  insert_pt : ident;
  delete_pt : ident;
  lookup_pt : ident;
  (* -- predicates -- *)
  is_page_table: gmap int32 addr → iProp Σ;
  (* -- operation specs -- *)
  insert_pt_spec i l m Φ ks:
    is_page_table m ∗ (is_page_table (<[ i := l ]> m) -∗ Φ Vvoid)
    ⊢ WP (Ecall Tvoid insert_pt [Evalue (Vint32 i); Evalue (Vptr l)], ks) {{ Φ }};
  delete_pt_spec i m Φ ks:
    is_page_table m ∗ (is_page_table (delete i m) -∗ Φ Vvoid)
    ⊢ WP (Ecall Tvoid delete_pt [Evalue (Vint32 i)], ks) {{ Φ }};
  lookup_pt_spec i m Φ ks:
    is_page_table m ∗ (is_page_table m -∗ Φ (option_addr_to_val (m !! i)))
    ⊢ WP (Ecall (Tptr Tvoid) lookup_pt [Evalue (Vint32 i)], ks) {{ Φ }}
}.

Arguments insert_pt {_ _} _.
Arguments delete_pt {_ _} _.
Arguments lookup_pt {_ _} _.
Arguments insert_pt_spec {_ _} _ _ _ _ _ _.
Arguments delete_pt_spec {_ _} _ _ _ _ _.
Arguments lookup_pt_spec {_ _} _ _ _ _ _.
Arguments is_page_table {_ _} _ _.

