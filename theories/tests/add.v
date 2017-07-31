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
  Definition I := (∃ vy, py ↦ Vint8 vy @ Tint8 ∗ own_sstate {[ "Y" := Vint8 vy ]})%I.

  Definition invs (prio: nat) : iProp Σ :=
    match prio with
      | O => I
      | _ => True%I
    end.

  Context `{i: interrupt invs 1}.

  Definition f_body : expr :=
    cli i ;;
    py <- !py@Tint8 + !"x"@Tint8 ;;
    "x" <- !py@Tint8 ;;
    sti i ;;
    return: !"x"@Tint8.

  Definition f_rel (vx: int8) (s: spec_state) (r: option val) (s': spec_state) :=
    ∃ vy:int8, s !! "Y" = Some (Vint8 vy) ∧
              r = Some (Vint8 (Byte.add vx vy)) ∧
              s' = <[ "Y" := (Vint8 (Byte.add vx vy)) ]> s.

  Definition int_ctx := @interrupt.int_ctx _ _ invs 1 i.

  Lemma f_spec γ γp f vx Φ k ks:
    f T↦ Function Tint8 [("x", Tptr Tint8)] f_body ∗
    int_ctx γ γp ∗ inv N spec_inv ∗ hpri invs γp 1 ∗
    own_scode (SCrel (f_rel vx)) ∗
    (∀ v, own_scode (SCdone (Some v)) -∗ hpri invs γp 1 -∗
          WP (fill_ectxs (Evalue v) k, ks) {{ _, Φ }})
    ⊢ WP (fill_ectxs (Ecall Tint8 f
                            (Epair (Ealloc Tint8 vx) void)) k, ks) {{ _, Φ }}.
  Proof.
    iIntros "(? & #? & #? & Hp & Hsc & HΦ)".
    rewrite (fill_app (Ealloc Tint8 vx)
                      [EKcall Tint8 f; EKpairl void ] k).
    iApply wp_bind=>//.
    wp_alloc x as "Hx".
    iApply wp_value=>//.
    rewrite -(fill_app x [EKcall Tint8 f; EKpairl void ] k).
    simpl.
    rewrite (fill_app (Epair x void)
                      [EKcall Tint8 f] k).
    iApply wp_bind=>//.
    iApply wp_pair.
    rewrite -(fill_app (Vpair x void) [EKcall Tint8 f] k).
    simpl.
    destruct ks.
    iApply (wp_call (sset "x" (Tptr Tint8, Vptr x) semp)
                    e _ (Vpair (Vptr x) Vvoid) [("x", Tptr Tint8)] f_body)=>//.
    iFrame. iIntros "!>".
    iApply wp_seq=>//.
    iApply cli_spec. iFrame "#". iFrame.
    iIntros "HI Hp Hcl".
    iDestruct "HI" as (vy) "[Hy HY]". iApply fupd_wp.
    (* Open invariant *)
    iInv N as ">Hspec" "Hclose".
    iMod (spec_update {[ "Y" := Vint8 vy ]} {[ "Y" := Vint8 (Byte.add vx vy) ]}
          with "[Hspec HY Hsc]")
      as "(Hspec & Hss' & Hsc' & ?)"; [ | iFrame; by iApply mapsto_singleton | ].
    { apply spec_step_rel'. unfold f_rel. eexists _. by gmap_simplify. }
    (* close invariant *)
    iMod ("Hclose" with "[Hspec]"); first eauto. iModIntro.
    wp_run. wp_var. wp_run. wp_var. wp_run. wp_var. wp_run.
    iApply ("HΦ" with "[-Hp]")=>//. by rewrite Byte.add_commut.
  Qed.

End example.
