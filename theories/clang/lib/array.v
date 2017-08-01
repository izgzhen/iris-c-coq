From iris_c.clang Require Import logic tactics notations.
From iris_c.lib Require Import int.

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

  Definition index (t: type) (p: addr) (ei: expr) : expr :=
    p + (Byte.repr (sizeof t) * ei).

  Fixpoint slice q t b o (i l: nat) vs : iProp Σ :=
    (match l, vs with
       | O, [] => True
       | S l', v::vs' => (b, o + sizeof t * i) ↦{q} v @ t ∗
                         slice q t b o(S i) l'  vs'
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
        iFrame. rewrite comm_assoc_s.
        iAssert (⌜length vs1 = l1'⌝ ∗
                 slice q t b o (S i) (l1' + l2) (vs1 ++ vs2))%I
          with "[-]" as "[% ?]".
        { iApply IHl1'. iFrame. }
        iFrame. by subst.
      + iIntros "[% Hs]".
        simpl. destruct vs1=>//; simpl in *.
        simplify_eq.
        iDestruct "Hs" as "[? ?]". iFrame. rewrite comm_assoc_s.
        iApply IHl1'. iSplit=>//.
  Qed.

  Lemma split_slice_join q t b o l1 i i' l2 vs1 vs2:
    i + l1 = i' →
    slice q t b o i l1 vs1 ∗ slice q t b o i' l2 vs2 ⊢
    slice q t b o i (l1 + l2) (vs1 ++ vs2).
  Proof. iIntros (?) "~". rewrite -H0.
         by iDestruct (split_slice with "~") as "[_ ?]". Qed.

  Lemma split_slice' q t b o k n vs:
    k < n → length vs = n →
    slice q t b o 0 k (take k vs) ∗ slice q t b o k (n - k) (drop k vs) ⊣⊢
    slice q t b o 0 n vs.
  Proof.
    intros ??.
    rewrite -{3}(take_drop k vs).
    assert (n = k + (n - k)) as H2; first omega.
    rewrite {2}H2.
    assert (k = 0 + k) as H3; first omega.
    rewrite {3}H3.
    iSplit.
    - iIntros "?". by iDestruct (split_slice with "~") as "[% ?]".
    - iIntros "?". iApply split_slice. iFrame.
      iPureIntro. apply take_length_le. rewrite H1. omega.
  Qed.

  Definition slice' q p t i l vs := let '(b, o) := p in slice q t b o i l vs.

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
    - iIntros (???).
      iSplit; iIntros "?"; destruct l=>//; simpl;
      rewrite assoc_s -distri_one; assoc_nat;
      iDestruct "~" as "[? ?]"; iFrame; by iApply IHvs'.
  Qed.

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
        replace (o + sizeof_type t * i + sizeof_type t)
          with (o + sizeof_type t * S i).
        iDestruct (IHn' with "H2") as "?". done.
        { replace (S i) with (i + 1); last omega.
          rewrite -distri_one. omega. }
      + iIntros "Hs". simpl.
        destruct vs=>//; first by iDestruct "Hs" as "%".
        simpl. iApply mapstoval_join. iDestruct "Hs" as "[? ?]".
        iFrame. simpl.
        replace (o + sizeof_type t * i + sizeof_type t)
          with (o + sizeof_type t * S i).
        by iApply IHn'.
        { replace (S i) with (i + 1); last omega.
          rewrite -distri_one. omega. }
  Qed.

  Lemma array_slice' q t n vs b o:
    (b, o) ↦{q} varray vs @ tyarray t n ⊣⊢ slice q t b o 0 n vs.
  Proof. assert (o = o + sizeof_type t * 0) as Ho.
         { rewrite Nat.mul_0_r Nat.add_0_r. done. }
         rewrite {1}Ho.
         apply array_slice. Qed.

  Lemma len_slice q t b o n vs:
    slice q t b o 0 n vs ⊢ ⌜ length vs = n ⌝.
  Proof.
    iIntros "?". iDestruct (array_slice' with "~") as "~".
    iDestruct (mapsto_typeof with "~") as "%".
    iPureIntro. by eapply len_varray.
  Qed.
  
  Lemma index_spec q t p (i n: nat) vs Φ ks:
    i < n → mul_safe (sizeof_type t) i →
    p ↦{q} varray vs @ tyarray t n ∗
    (∀ v, p ↦{q} varray vs @ tyarray t n -∗ ⌜ vs !! i = Some v⌝ -∗ Φ v)
    ⊢ WP (!(index t p (Vint8 (Byte.repr i)))@t, ks) {{ Φ }}.
  Proof.
    iIntros (??) "[Hp HΦ]". destruct p.
    iDestruct (array_slice' with "Hp") as "Hs".
    destruct i.
    - unfold index. wp_op. rewrite_byte.
      wp_op. rewrite_byte.
      destruct n.
      { inversion H0. }
      destruct vs=>//; first by iDestruct "Hs" as "%".
      simpl.  iDestruct "Hs" as "[? ?]".
      rewrite_nat.  wp_load.
      iApply wp_value=>//. iApply ("HΦ" with "[-]")=>//.
      iApply mapstoval_join. iFrame.
      simpl. iDestruct (array_slice with "~") as "?".
      by rewrite_nat.
    - unfold index. wp_op.
      wp_op. rewrite /offset_by_byte. rewrite H1.
      iDestruct (len_slice with "Hs") as "%".
      iDestruct (split_slice' _ _ b o (S i) n vs with "[Hs]") as "[? ?]"=>//.
      simpl. destruct (n - S i) eqn:?.
      { exfalso. omega. }
      destruct (drop (S i) vs) eqn:?.
      { exfalso. assert (length (drop (S i) vs) = 0).
        { by rewrite Heql. }
        rewrite drop_length in H3. rewrite H2 in H3.
        omega.
      }
      simpl. iDestruct "~1" as "[? ?]".
      wp_load. iApply wp_value=>//.
      iApply ("HΦ" with "[-]").
      + iApply array_slice'.
        iDestruct (single_slice with "~1") as "Hm".
        destruct (take (S i) vs) eqn:?.
        { by iDestruct "~" as "%". }
        iDestruct "~" as "[H1 H2]".
        iDestruct (single_slice with "H1") as "H0".
        iDestruct (split_slice_join with "[H2 H0]") as "?"; [|iFrame|]; first omega.
        iDestruct (split_slice_join with "[Hm ~]") as "?"; [|iFrame|]; first omega.
        iDestruct (split_slice_join with "[~2 ~1]") as "?"; [|iFrame|]; first omega.
        replace (1 + i + 1 + n0) with n; last omega.
        replace ((([v0] ++ l0) ++ [v]) ++ l) with vs=>//.
        rewrite -assoc.
        rewrite !app_cons. rewrite -Heql -Heql0.
        by rewrite take_drop.
      + destruct (vs !! S i) eqn:?.
        * iPureIntro. f_equal.
          move:(take_drop_middle _ _ _ Heqo0)=>H3.
          rewrite -H3 in Heql.
          rewrite take_drop_app in Heql=>//.
          { by inversion Heql. }
          rewrite H2. omega.
        * rewrite -H2 in H0. apply lookup_lt_is_Some in H0.
          iPureIntro. inversion H0. rewrite H3 in Heqo0. done.
  Qed.

End array.
