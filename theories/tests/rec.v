From iris_c.clang Require Import notations lang logic tactics.
From iris_c.lib Require Import int.

Section proof.
  Context `{clangG Σ}.

  Definition f : expr :=
    if: (!"x"@Tint8 != 0)
    then: (
      "x" <- !"x"@Tint8 - 1 ;;
      Ecall Tvoid "g" (Epair (Evar "x") (Evalue Vvoid)) ;;
      return: void)
    else: ( return: void ).

  Definition g : expr :=
    if: (!"x"@Tint8 != 0)
    then: (
      "x" <- !"x"@Tint8 - 1 ;;
      Ecall Tvoid "f" (Epair (Evar "x") (Evalue Vvoid));;
      return: void)
    else: ( return: void ).

  Definition rec_env n : env := (sset "x" (Tptr Tint8, Vptr n) semp).

  Definition Pn : Prop :=
    (∀ n: nat, Byte.repr n = ((Z.pos (Pos.of_succ_nat n) - 1%Z)%int)) ∧
    (∀ n: nat, evalbop oneq (Z.pos (Pos.of_succ_nat n)) 0%Z = Some vtrue).
  
  Lemma rec_example (ln: addr) (n: nat) k ks Φ:
    Pn →
    ln ↦ n @ Tint8 ∗
    "f" T↦ Function Tvoid [("x", Tptr Tint8)] f ∗
    "g" T↦ Function Tvoid [("x", Tptr Tint8)] g ∗ (WP (fill_ectxs void k, ks) {{ Φ }})
    ⊢ WP (fill_ectxs (Ecall Tvoid "f"
                            (Evalue (Vpair ln void))) k, ks) {{ Φ }}.
  Proof.
    iIntros (Hn) "[Hn [#? [#? HΦ]]]".
    iLöb as "IH" forall (n k ks Φ Hn). destruct ks.
    iApply (wp_call (rec_env ln) e _ (Vpair ln Vvoid) [("x", Tptr Tint8)])=>//.
    destruct n eqn:?; subst; iFrame "#"; iNext.
    - unfold f. wp_var. by wp_run.
    - unfold f. wp_var. wp_run=>//.
      { destruct Hn as [H1 H2].
        specialize H2 with n0. done. }
      wp_step. iNext. wp_var. wp_var. wp_run.
      wp_unfill (Ecall _ _ _).
      rewrite (fill_app (Evar "x")
                        [EKcall Tvoid "g"; EKpairl void]).
      iApply wp_bind=>//.
      wp_var. iApply wp_value=>//.
      wp_unfill (Ecall _ _ _).
      rewrite (fill_app (Epair ln void)
                        [EKcall Tvoid "g"]).
      iApply wp_bind=>//. wp_pair.
      iApply wp_value=>//.
      replace ((Z.pos (Pos.of_succ_nat n0) - 1%Z)%int)
        with (Byte.repr n0).
      iApply (wp_call (rec_env ln) (rec_env ln)
                         [EKseq (return: void)] (Vpair ln void)
                         [("x", Tptr Tint8)]);
        last iFrame "#"; first done.
      iNext. unfold g. wp_var. wp_load.
      destruct n0 eqn:Heqn; subst.
      + wp_run. simpl. wp_run. done.
      + simpl.
        wp_op=>//.
        { destruct Hn as [H1 H2]. simpl. apply H2. }
        wp_step. iApply wp_seq=>//. wp_run.
        wp_unfill (Ecall _ _ _)%E.
        rewrite (fill_app (Evar "x")
                          [EKcall Tvoid "f"; EKpairl void]).
        iApply wp_bind=>//.
        wp_var. iApply wp_value=>//.
        wp_unfill (Ecall _ _ _).
        rewrite (fill_app (Epair ln void) [EKcall Tvoid "f"]).
        iApply wp_bind=>//. wp_pair.
        iApply wp_value=>//.
        wp_unfill (Ecall _ _ _).
        replace (Z.pos (Pos.of_succ_nat n) - 1%Z)%int
        with (Byte.repr n).
        iDestruct ("IH" $! n) as "IH'".
        iDestruct ("IH'" $! _ _ _ with "[]") as "?"=>//.
        iApply ("~2" with "[-HΦ]")=>//.
        simpl. wp_run. simpl. wp_run.
        { by destruct Hn as [? ?]. }
        { by destruct Hn as [? ?]. }
      + by destruct Hn as [? ?].
  Qed.

End proof.
