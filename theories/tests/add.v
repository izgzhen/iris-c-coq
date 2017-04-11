From iris.base_logic.lib Require Export wsat.
From iris_os.clang Require Import logic tactics notations.
From iris.base_logic Require Import big_op.
From iris_os.os Require Import spec interrupt.
Require Import lib.gmap_solve.
From iris.proofmode Require Export tactics.
Set Default Proof Using "Type".

Section example.
  Context `{clangG Σ, specG Σ} {N: namespace}.

  Parameter px py: addr.
  Definition x: ident := 1.
  Definition y: ident := 3.
  Definition Y: ident := 2.
  Definition I := (∃ vy, py ↦ Vint32 vy @ Tint32 ∗ Y S↦ Vint32 vy)%I.

  Definition invs (prio: nat) : iProp Σ :=
    match prio with
      | O => I
      | _ => True%I
    end.

  Context `{i: interrupt invs}.

  Definition f_body : expr :=
    cli ;;
    y <- y + x ;;
    x <- y ;;
    sti ;;
    rete x.

  Definition f_rel (vx: int) (s: spec_state) (r: option val) (s': spec_state) :=
    ∃ vy:int, s !! Y = Some (Vint32 vy) ∧
              r = Some (Vint32 (Int.add vx vy)) ∧
              s' = <[ Y := (Vint32 (Int.add vx vy)) ]> s.

  Definition int_ctx := @interrupt.int_ctx _ _ invs i.

  Lemma f_spec γ γp f vx Φ k ks:
    text_interp f (Function Tint32 [(x, Tint32); (y, Tint32)] f_body)  ∗
    int_ctx N γ γp ∗ inv N spec_inv ∗ hpri invs γp 1 ∗ stack_interp ks ∗
    scode (SCrel (f_rel vx)) ∗ px ↦ vx @ Tint32 ∗
    (∀ v, scode (SCdone (Some v)) -∗ hpri invs γp 1 -∗ stack_interp ks -∗ WP (fill_ectxs (Evalue v) k) {{ _, Φ }})
    ⊢ WP fill_ectxs (Ecall f [Evalue (Vptr px); Evalue (Vptr py)]) k {{ _, Φ }}.
  Proof.
    iIntros "(? & #? & #? & Hp & Hs & Hsc & Hx & HΦ)".
    iApply (wp_call ⊤ _ _ _ [px; py] [(x, Tint32); (y, Tint32)] f_body)=>//.
    iFrame. iNext. iIntros "Hstk". iApply wp_seq=>//.
    iApply cli_spec. iFrame "#". iFrame.
    iIntros "HI Hp Hcl".
    iDestruct "HI" as (vy) "[Hy HY]". iApply fupd_wp.
    (* Open invariant *)
    iInv N as ">Hspec" "Hclose".
    iMod (spec_update {[ Y := Vint32 vy ]} _ {[ Y := Vint32 (Int.add vx vy) ]}
               with "[Hspec HY Hsc]")
      as (?) "(Hspec & Hss' & Hsc' & ?)"; [ | iFrame; by iApply mapsto_singleton | ].
    { apply spec_step_rel'. unfold f_rel.
      exists vy. by gmap_simplify. }
    (* close invariant *)
    iMod ("Hclose" with "[Hspec]"); first eauto. iModIntro.
    wp_run. iApply wp_seq=>//. iApply sti_spec.
    iFrame. iFrame "#".  iSplitL "Hss' Hy".
    { iExists (Int.add vy vx). iFrame.
      rewrite Int.add_commut. by iApply mapsto_singleton. }
    iIntros "Hp". wp_skip. wp_load. iApply (wp_ret []). iFrame.
    iApply ("HΦ" with "[-Hp]")=>//. by rewrite Int.add_commut.
  Qed.

End example.
