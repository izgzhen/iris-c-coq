From iris_c.clang Require Import logic tactics notations.

(* Kinda funky -- but really extensible *)

Section array.
  Context `{clangG Σ}.

  Fixpoint tyarray (t: type) (n: nat) : type :=
    match n with
      | O => Tvoid
      | S n' => Tprod t (tyarray t n')
    end.

  Fixpoint varray (vs: list val) : val :=
    match vs with
      | [] => Vvoid
      | v::vs' => Vpair v $ varray vs'
    end.

  Lemma len_varray t: ∀ n vs,
    typeof (varray vs) (tyarray t n) → length vs = n.
  Proof.
    induction n as [|n' IHn'].
    - simpl. intros ?. destruct vs=>//. inversion 1.
    - simpl. intros vs H'.
      destruct vs=>//.
      { inversion H'. }
      simpl. f_equal. apply IHn'. inversion H'. simplify_eq. done.
  Qed.

  (* e should be a Tptr to some tyarray t n, which gives us some flexibility *)
  Definition index (t: type) (p: addr) (ei: expr) : expr := p + (Int.repr (sizeof t) <*> ei).

  Fixpoint slice q t b o (i l: nat) vs : iProp Σ :=
    (match l, vs with
       | O, [] => True
       | S l', v::vs' => (b, o + sizeof t * i) ↦{q} v @ t ∗ slice q t b o(S i) l'  vs'
       | _, _ => False%I
     end)%I.

  Lemma split_slice q t b o:
    ∀ l1 i l2 vs1 vs2,
      slice q t b o i l1 vs1 ∗ slice q t b o (i + l1) l2 vs2 ⊣⊢
      ⌜ length vs1 = l1 ⌝ ∗ slice q t b o i (l1 + l2) (vs1 ++ vs2).
  Proof.
    induction l1 as [|l1' IHl1'].
    - intros. iSplit.
      + iIntros "[Hs1 Hs2]".
        simpl. destruct vs1=>//; last by iDestruct "Hs1" as "%".
        simpl. replace (i + 0) with i=>//. by iFrame.
      + iIntros "Hs".
        simpl. destruct vs1=>//.
        * iDestruct "Hs" as "[_ ?]". simpl. replace (i + 0) with i=>//. by iFrame.
        * iDestruct "Hs" as "[% ?]". done.
    - intros. iSplit.
      + iIntros "[Hs1 Hs2]".
        destruct vs1=>//; simpl; first by iDestruct "Hs1" as "%".
        iDestruct "Hs1" as "[Hv Hl1']".
        iFrame.
        replace (i + S l1') with (S i + l1')=>//; last omega.
        iAssert (⌜length vs1 = l1'⌝ ∗ slice q t b o (S i) (l1' + l2) (vs1 ++ vs2))%I with "[-]" as "[% ?]".
        { iApply IHl1'. iFrame. }
        iFrame. by subst.
      + iIntros "[% Hs]".
        simpl. destruct vs1=>//; simpl in *.
        simplify_eq.
        iDestruct "Hs" as "[? ?]". iFrame.
        replace (i + S (length vs1)) with (S i + length vs1)=>//; last omega.
        iApply IHl1'.
        iSplit=>//.
  Qed.

  Definition slice' q p t i l vs := let '(b, o) := p in slice q t b o i l vs.

  Definition split_slice' q t p i l1 l2 vs1 vs2:
    slice' q p t i l1 vs1 ∗ slice' q p t (i + l1) l2 vs2 ⊣⊢
    ⌜ length vs1 = l1 ⌝ ∗ slice' q p t i (l1 + l2) (vs1 ++ vs2).
  Proof.
    destruct p. iSplit.
    - iIntros "[? ?]". iApply split_slice; iFrame.
    - iIntros "?". iApply split_slice; iFrame.
  Qed.

  Definition single_slice q b o t i v:
    slice q t b o i 1 [v] ⊣⊢ (b, o + sizeof t * i) ↦{q} v @ t.
  Proof.
    simpl. iSplit.
    - by iIntros "[? _]".
    - iIntros "?"; by iSplit.
  Qed.

  Lemma slice_move q t b:
    ∀ vs o l i,
      slice q t b (o + sizeof_type t) i l vs ⊣⊢
      slice q t b o (i + 1) l vs.
  Proof.
    induction vs as [|v' vs' IHvs'].
    - iIntros (???). iSplit; iIntros "?"; destruct l=>//.
    - iIntros (???). iSplit; iIntros "?"; destruct l=>//; simpl.
      + replace (o + sizeof_type t * (i + 1)) with (o + sizeof_type t + sizeof_type t * i).
        iDestruct "~" as "[? ?]". iFrame.
        replace (S (i + 1)) with (S i + 1). by iApply IHvs'.
        { omega. }
        { rewrite Nat.mul_add_distr_l -assoc Nat.mul_1_r. omega. }
      + replace (o + sizeof_type t * (i + 1)) with (o + sizeof_type t + sizeof_type t * i).
        iDestruct "~" as "[? ?]". iFrame.
        replace (S (i + 1)) with (S i + 1). by iApply IHvs'.
        { omega. }
        { rewrite Nat.mul_add_distr_l -assoc Nat.mul_1_r. omega. }
  Qed. (* FIXME: verbose *)

  Definition array_slice q t: ∀ n vs b o i,
    (b, o + sizeof_type t * i) ↦{q} varray vs @ tyarray t n ⊣⊢ slice q t b o i n vs.
  Proof.
    induction n as [|n' IHn'].
    - iIntros (????).
      unfold slice'. simpl. destruct vs=>//; simpl.
      + iSplit; auto.
        iIntros "_". rewrite /mapstoval. iSplit=>//.
      + iSplit; iIntros "H".
        * iDestruct (mapsto_typeof with "H") as "%".
          inversion H0.
        * by iDestruct "H" as "%".
    - iIntros (????).
      iSplit.
      + iIntros "H". simpl.
        destruct vs=>//.
        { simpl. iDestruct (mapsto_typeof with "H") as "%".
          inversion H0. }
        simpl.
        iDestruct (mapstoval_split with "H") as "[H1 H2]".
        iFrame. simpl.
        replace (o + sizeof_type t * i + sizeof_type t) with (o + sizeof_type t * S i).
        iDestruct (IHn' with "H2") as "?". done.
        admit.
      + iIntros "Hs". simpl.
        destruct vs=>//; first by iDestruct "Hs" as "%".
        simpl. iApply mapstoval_join. iDestruct "Hs" as "[? ?]".
        iFrame. simpl.
        replace (o + sizeof_type t * i + sizeof_type t) with (o + sizeof_type t * S i).
        by iApply IHn'.
        admit.
  Admitted.

  Lemma array_slice' q t n vs b o:
    (b, o) ↦{q} varray vs @ tyarray t n ⊣⊢ slice q t b o 0 n vs.
  Proof. Admitted.

  Lemma index_spec q t p i n vs Φ:
    i < n →
    p ↦{q} varray vs @ tyarray t n ∗ (∀ v, p ↦{q} varray vs @ tyarray t n -∗ ⌜ vs !! i = Some v⌝ -∗ Φ v)
    ⊢ WP !(index t p (Int.repr i))@t {{ Φ }}.
  Proof.
    iIntros (?) "[Hp HΦ]". destruct p.
    iDestruct (array_slice' with "Hp") as "Hs".
    destruct i.
    - unfold index. wp_op.
      rewrite Int.mul_zero. wp_op.
      rewrite /offset_by_int32.
      replace (Z.to_nat (Int.intval Int.zero)) with 0%nat; last done.
      replace (o + 0) with o=>//.
      destruct n.
      { inversion H0. }
      destruct vs=>//; first by iDestruct "Hs" as "%".
      simpl. rewrite Nat.mul_0_r Nat.add_0_r. iDestruct "Hs" as "[? ?]".
      wp_load. iApply wp_value=>//. iApply ("HΦ" with "[-]")=>//.
      iApply mapstoval_join. iFrame.
      simpl. iDestruct (array_slice with "~") as "?".
      rewrite Nat.mul_1_r. done.
    - unfold index. wp_op.
      wp_op. rewrite /offset_by_int32.
      replace (Z.to_nat (Int.intval (Int.mul (Int.repr (sizeof_type t))
                (Int.repr (Z.pos (Pos.of_succ_nat i))))))%nat with (sizeof_type t * S i).
      iDestruct (split_slice _ _ b o (S i) 0 (n - S i)
                             (take (S i) vs) (drop (S i) vs)
                 with "[Hs]") as "[? ?]".
      { admit. }
      simpl. destruct (n - S i) eqn:?.
      { admit. }
      destruct (drop (S i) vs) eqn:?.
      { admit. }
      simpl. iDestruct "~1" as "[? ?]".
      wp_load. iApply wp_value=>//.
      iApply ("HΦ" with "[-]").
  Admitted.

End array.
