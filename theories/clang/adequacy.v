From iris_os.clang Require Export logic.
From iris.algebra Require Import gmap auth agree gset coPset.
From iris.base_logic Require Import big_op soundness.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Import weakestpre adequacy.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class clangPreG Σ := ClangPreG {
  clang_preG_iris :> invPreG Σ;
  clang_preG_clang :> gen_heapPreG addr byteval Σ;
  clangG_preG_textG :> inG Σ textG;
  clangG_preG_stackG :> inG Σ stackG;
}.

Definition clangΣ : gFunctors := #[invΣ; gen_heapΣ addr byteval; GFunctor textG; GFunctor stackG].
Instance subG_clangPreG {Σ} : subG clangΣ Σ → clangPreG Σ.
Proof. solve_inG. Qed.

Definition clang_adequacy Σ `{clangPreG Σ} e σ φ :
  (∀ `{clangG Σ}, True ⊢ WP e {{ v, ⌜φ v⌝ }}) →
  adequate e σ φ.
Proof.
  intros Hwp; eapply (wp_adequacy Σ _); iIntros (?) "".
  iMod (own_alloc (● to_gen_heap (s_heap σ))) as (γ) "Hh".
  { apply: auth_auth_valid. exact: to_gen_heap_valid. }
  iMod (own_alloc (● to_gen_text (s_text σ))) as (γ') "Ht".
  { apply: auth_auth_valid. intros l. rewrite lookup_fmap. by case (s_text σ !! l).  }
  iMod (own_alloc (to_gen_stack (s_stack σ))) as (γ'') "Hs".
  { split=>//. }
  iModIntro. iExists (fun σ => own γ (● to_gen_heap (s_heap σ)) ∗
                               own γ' (● to_gen_text (s_text σ)) ∗
                               own γ'' (to_gen_stack (s_stack σ)))%I.
  set (Hheap := GenHeapG addr byteval Σ _ _ _ γ).
  iFrame. iApply (Hwp (ClangG _ _ _ _ γ' _ γ'')).
Qed.
