From iris_os.clang Require Import logic tactics notations.
From iris.base_logic Require Import big_op.
From iris_os.os Require Import spec interrupt.
Require Import lib.gmap_solve.
Set Default Proof Using "Type".

Section example.
  Context `{clangG Σ, specG Σ} {N: namespace}.

  Parameter py: addr.
  Parameter x Y lock unlock: ident.
  Definition I := (∃ vy, py ↦ Vint32 vy @ Tint32 ∗ Y S↦ Vint32 vy)%I.  

  Definition invs (prio: nat) : iProp Σ :=
    match prio with
      | 0 => I
      | _ => True%I
    end.

  Context `{i: interrupt invs}.

  Definition f_body : stmts :=
    cli ;;
    py <- !py + x ;;
    x <- !py ;;
    sti ;;
    rete x.

  Definition f_rel (vx: int) (s: spec_state) (r: option val) (s': spec_state) :=
    ∃ vy:int, s !! Y = Some (Vint32 vy) ∧
              r = Some (Vint32 (Int.add vx vy)) ∧
              s' = <[ Y := (Vint32 (Int.add vx vy)) ]> s.

  Definition int_ctx := @int_ctx _ _ invs i.

  Lemma f_spec (p: program) γ γp f vx Φ Φret:
    p f = Some (Tint32, [(x, Tint32)], f_body) →
    int_ctx N γ γp ∗ inv N spec_inv ∗ hpri invs γp 1 ∗
    scode (SCrel (f_rel vx)) ∗ (∀ v, scode (SCdone (Some v)) -∗ hpri invs γp 1 -∗ Φ)
    ⊢ WP curs (Scall f [Evalue (Vint32 vx)]) {{ _, Φ ; Φret }}.
  Proof.
    iIntros (Hpf) "(#? & #? & Hp & Hsc & HΦ)".
    iApply (wp_call _ _ [Vint32 vx])=>//.
    { simpl. split=>//. constructor. }
    iIntros (ls) "% Hls".
    destruct ls as [|? [|? ls]].
    - simpl. iDestruct "Hls" as "%"=>//. by iIntros "%".
    - unfold_f_inst. gmap_rewrite.
      destruct (decide (x = x))=>//.
      iDestruct "Hls" as "[_ %]".
      inversion H1; subst.
      iIntros "[Hvx _]".
      wp_run. iApply cli_spec.
      iFrame "#". iFrame.  iIntros "HI Hp Hcl".
      iDestruct "HI" as (vy) "[Hy HY]". iApply fupd_wp.
      (* Open invariant *)
      iInv N as ">Hspec" "Hclose".
      iDestruct (spec_update {[ Y := Vint32 vy ]} _ {[ Y := Vint32 (Int.add vx vy) ]}
                 with "[Hspec HY Hsc]")
        as "(Hspec & Hss' & Hsc')".
      { iFrame "Hspec". iSplitL "HY"; first by iApply mapsto_singleton.
        iFrame "Hsc". 
        iPureIntro. apply spec_step_rel. unfold f_rel.
        exists vy. gmap_simplify=>//. by gmap_rewrite. }
      (* close invariant *)
      iMod ("Hclose" with "[Hspec]"); first eauto. iModIntro.
      wp_run. iApply sti_spec.
      iFrame. iFrame "#".  iSplitL "Hss' Hy".
      { iExists (Int.add vy vx). iFrame. rewrite Int.add_commut. by iApply mapsto_singleton. }
      iIntros "Hp". wp_run. iApply wp_ret.
      iApply ("HΦ" with "[-Hp]")=>//.
    - iDestruct "Hls" as "[% _]". inversion H1.
  Qed.

End example.
