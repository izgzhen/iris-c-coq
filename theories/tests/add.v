From iris.base_logic.lib Require Export wsat.
From iris_c.clang Require Import logic tactics notations.
From iris.base_logic Require Import big_op.
From iris_c.clang.lib Require Import refine interrupt.
Require Import lib.gmap_solve.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".

Section example.
  Context `{clangG Σ, refineG Σ} {N: namespace}.

  Parameter py: addr.
  Definition x: ident := 1.
  Definition Y: ident := 2.
  Definition I := (∃ vy, py ↦ Vint32 vy @ Tint32 ∗ own_sstate {[ Y := Vint32 vy ]})%I.

  Definition invs (prio: nat) : iProp Σ :=
    match prio with
      | O => I
      | _ => True%I
    end.

  Context `{i: interrupt invs 1}.

  Definition f_body : expr :=
    cli i ;;
    py <- !py@Tint32 + x ;;
    x <- !py@Tint32 ;;
    sti i ;;
    return: x.

  Definition f_rel (vx: int) (s: spec_state) (r: option val) (s': spec_state) :=
    ∃ vy:int, s !! Y = Some (Vint32 vy) ∧
              r = Some (Vint32 (Int.add vx vy)) ∧
              s' = <[ Y := (Vint32 (Int.add vx vy)) ]> s.

  Definition int_ctx := @interrupt.int_ctx _ _ invs 1 i.

  Lemma f_spec γ γp f vx Φ k ks:
    text_interp f (Function Tint32 [(x, Tint32)] f_body)  ∗
    int_ctx γ γp ∗ inv N spec_inv ∗ hpri invs γp 1 ∗ own_stack ks ∗
    own_scode (SCrel (f_rel vx)) ∗
    (∀ v, own_scode (SCdone (Some v)) -∗ hpri invs γp 1 -∗ own_stack ks -∗
          WP (fill_ectxs (Evalue v) k) {{ _, Φ }})
    ⊢ WP fill_ectxs (Ecall_typed Tint32 f [Evalue vx]) k {{ _, Φ }}.
  Proof.
    iIntros "(? & #? & #? & Hp & Hs & Hsc & HΦ)".
    iApply (wp_call _ [Vint32 vx] [(x, Tint32)] f_body)=>//.
    iFrame. iNext. iIntros "Hstk".
    wp_alloc px as "Hpx". wp_let. iApply wp_seq=>//.
    iApply cli_spec. iFrame "#". iFrame.
    iIntros "HI Hp Hcl".
    iDestruct "HI" as (vy) "[Hy HY]". iApply fupd_wp.
    (* Open invariant *)
    iInv N as ">Hspec" "Hclose".
    iMod (spec_update {[ Y := Vint32 vy ]} {[ Y := Vint32 (Int.add vx vy) ]} with "[Hspec HY Hsc]")
      as "(Hspec & Hss' & Hsc' & ?)"; [ | iFrame; by iApply mapsto_singleton | ].
    { apply spec_step_rel'. unfold f_rel. eexists _. by gmap_simplify. }
    (* close invariant *)
    iMod ("Hclose" with "[Hspec]"); first eauto. iModIntro.
    wp_run. iFrame. iApply ("HΦ" with "[-Hp]")=>//. by rewrite Int.add_commut.
  Qed.

End example.
