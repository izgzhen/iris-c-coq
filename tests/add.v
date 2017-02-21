From iris_os.clang Require Import lang logic.
From iris.base_logic Require Import big_op.
From iris_os.os Require Import spec.
From iris.proofmode Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Section example.
  Context `{clangG Σ, specG Σ} {N: namespace}.
  
  Parameter py: addr.
  Parameter Y lock unlock: ident.

  Definition y := Evalue (Vptr py).
  
  Definition f_body (px: addr) : stmts :=
    Scall lock [] ;;;
    Sassign y (Ebinop oplus (Ederef y) (Ederef (Evalue (Vptr px)))) ;;;
    Sassign (Evalue (Vptr px)) (Ederef y) ;;;
    Scall unlock [] ;;;
    Srete (Ederef (Evalue (Vptr px))).

  Definition f_body' (x: ident) : stmts :=
    Scall lock [] ;;;
    Sassign y (Ebinop oplus (Ederef y) (Evar x)) ;;;
    Sassign (Evar x) (Ederef y) ;;;
    Scall unlock [] ;;;
    Srete (Evar x).

  Definition f_rel (vx: int) (s: spec_state) (r: option val) (s': spec_state) :=
    ∃ vy:int, s !! Y = Some (Vint32 vy) ∧
              r = Some (Vint32 (Int.add vx vy)) ∧
              s' = <[ Y := (Vint32 (Int.add vx vy)) ]> s.

  Definition I := (∃ vy, py ↦ Vint32 vy @ Tint32 ∗ Y S↦ Vint32 vy)%I.

  (* XXX: very naive *)
  
  Lemma lock_spec Φ Φret:
    (I -∗ Φ) ⊢ WP (curs (Scall lock []), knil) {{ _, Φ; Φret }}.
  Admitted.

  Lemma unlock_spec Φ Φret:
    I ∗ (True -∗ Φ) ⊢ WP (curs (Scall unlock []), knil) {{ _, Φ; Φret }}.
  Admitted.

  Lemma mapsto_singleton l v:
    l S↦ v ⊣⊢ sstate {[ l := v ]}.
  Proof. by rewrite /sstate big_sepM_singleton. Qed.
  
  Lemma f_spec px vx Φ Φret:
    inv N spec_inv ∗
    px ↦ Vint32 vx @ Tint32 ∗ scode (SCrel (f_rel vx)) ∗
    (∀ v, px ↦ v @ Tint32 -∗ scode (SCdone (Some v)) -∗ Φret (Some v))
    ⊢ WP (curs (f_body px), knil) {{ Φ ; Φret }}.
  Proof.
    iIntros "(#? & Hx & Hsc & HΦret)".
    iApply wp_seq. iApply lock_spec. iIntros "HI".
    iDestruct "HI" as (vy) "[Hy HY]". iApply fupd_wp.
    (* Open invariant *)
    iInv N as ">Hspec" "Hclose".
    iDestruct (spec_update with "[Hspec HY Hsc]") as "(Hspec & Hss' & Hsc')".
    { iFrame "Hspec". iSplitL "HY"; first by iApply mapsto_singleton.
      iFrame "Hsc". 
      iPureIntro.
      apply spec_step_rel. unfold f_rel.
      exists vy. admit.
    }
    iMod ("Hclose" with "[Hspec]"); first eauto. iModIntro.
    iApply wp_seq.
    rewrite /example.y.
    iApply (wp_bind_s _ (SKassignl _)).
    iApply (wp_bind _ (EKbinopr _ _)).
    iApply wp_conte.
    iApply wp_load. iFrame "Hy". iIntros "Hy". (* XXX: use wp_load tactic *)
    iApply (wp_unbind _ (EKbinopr _ _)).
    simpl. iApply (wp_bind _ (EKbinopl _ _)).
    iApply wp_conte.
    iApply wp_load. iFrame "Hx". iIntros "Hx".
    iApply (wp_unbind _ (EKbinopl _ _)).
    simpl.
    iApply wp_conte.
    iApply wp_op=>//.
    iApply (wp_unbind_s _ (SKassignl _)).
    simpl.
    iApply wp_assign; first by apply typeof_int32.
    iSplitL "Hy"; first eauto.
    iIntros "Hy".
    iApply wp_seq.
    iApply (wp_bind_s _ (SKassignl _)).
    iApply wp_conte.
    iApply wp_load. iFrame "Hy". iIntros "Hy".
    iApply (wp_unbind_s _ (SKassignl _)).
    simpl. iApply wp_assign; first by apply typeof_int32.
    iSplitL "Hx"; first eauto. iIntros "Hx".
    iApply wp_seq. iApply unlock_spec.
    iSplitL "Hss' Hy".
    { iExists (Int.add vy vx). iFrame. by iApply mapsto_singleton. }
    iIntros "_".
    iApply (wp_bind_s _ SKrete).
    iApply wp_conte. iApply wp_load.
    iFrame "Hx". iIntros "Hx".
    iApply (wp_unbind_s _ SKrete). simpl.
    iApply wp_ret.
    iSpecialize ("HΦret" $! (Vint32 (Int.add vy vx)) with "Hx").
    by iApply "HΦret".
  Admitted.
  
  Lemma f_spec' (p: program) (x: ident) f vx Φ Φret:
    p f = Some (Tint32, [(x, Tint32)], f_body' x) →
    inv N spec_inv ∗
    scode (SCrel (f_rel vx)) ∗ (∀ v, scode (SCdone (Some v)) -∗ Φ)
    ⊢ WP (curs (Scall f [Evalue (Vint32 vx)]), knil) {{ _, Φ ; Φret }}.
  Proof.
    iIntros (Hpf) "(#? & Hsc & HΦ)".
    iApply (wp_call _ _ [Vint32 vx])=>//.
    { simpl. split=>//. apply typeof_int32. }
    iIntros (ls) "% Hls".
    destruct ls as [|a [|b ls]].
    - simpl. iDestruct "Hls" as "%"=>//.
    - simpl. destruct (decide (x = x))=>//.
      iDestruct "Hls" as "[Hx _]".
      iApply f_spec. iFrame "#". iFrame.
      iIntros (v) "_ Hsc". (* XXX: free *)
      iApply wp_skip.
      by iApply "HΦ".
    - inversion H1.
  Qed.

End example.
