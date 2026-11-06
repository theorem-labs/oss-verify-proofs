(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxAcct.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AsanWAcc AxLazy AxLin AxVal AxBytes AxMem AxZZ AxState AxSys AxMeasure AxSysNode AxSysMmap AxGrant AxSysFix AxSysProt0 AxPostFix.
From OSSVerify.Proofs.openssl.bndiv.lib.VCommon.Ax Require Import AxFd AxModelRel AxMRFix AxSys2B AxSysFixS.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

Section Main.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg2 : sc_alloc cfg = false.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.
Hypothesis Hlow : segs_low segs.

Notation MRm := (MR segs fs0).
Notation RR ρ := (R segs amodel (MRm ρ) LIM ρ).

Lemma prot_vmmaps (m : Model) (a n : word) :
  m_vmmaps (mprotect_model_next m a n)
  = mkVmMapsFull (vm_reserved (m_vmmaps m)) (vm_maps (m_vmmaps m))
      (maps_subtract (vm_noaccess (m_vmmaps m)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
      (vm_start_brk (m_vmmaps m)) (vm_brk (m_vmmaps m)) (vm_limit (m_vmmaps m)) (vm_mmap_base (m_vmmaps m)) (vm_init_sp (m_vmmaps m)).
Proof. unfold mprotect_model_next. cbv zeta. apply with_vmmaps_vmmaps_eq. Qed.

Theorem sys_mprotect2_sound (A : AST) (l : list AST) :
  pc_ok (npc A) = true -> xlit (aget (a_regs A) 17%uint63) = Some 226 -> sys_mprotect2 LIM A = Some l ->
  (forall B, In B l -> forall ρ c, RR ρ B c -> forall o, out_val ρ B o -> realizes_cfg segs cfg c (KT ρ o)) ->
  forall ρ c, RR ρ A c -> (exists w, fetch_word segs (ms_pc_val (cfg_ms c)) = Some w /\ is_ecall w = true) ->
  forall o, out_val ρ A o -> realizes_cfg segs cfg c (KT ρ o).
Proof.
  intros Hpc H17 Hsys HS ρ [ms model] HR [w [Hf He]] o Ho. cbn [cfg_ms] in Hf.
  unfold sys_mprotect2 in Hsys.
  destruct (len_shape A) as [nZ|] eqn:Esh; [|discriminate Hsys].
  destruct (xlit (aget (a_regs A) 12%uint63)) as [prot|] eqn:L12; [|discriminate Hsys].
  assert (Ep : prot = 3) by (destruct prot as [|p|p]; try discriminate Hsys; do 2 (destruct p; try discriminate Hsys); reflexivity).
  subst prot.
  destruct (xform (a_facts A) (aget (a_regs A) 10%uint63)) as [f|] eqn:Ef; [|discriminate Hsys].
  destruct (find_ent (a_facts A) f nZ (am_maps (a_model A))) as [e0|] eqn:Ee; [|discriminate Hsys].
  destruct (expose_ok A f nZ e0 &&& no_exp e0 (am_exp (a_model A)) &&& (a_budget A + nZ <=? LIM)) eqn:Ec; [|discriminate Hsys].
  injection Hsys as <-.
  apply andb_prop in Ec as [Ec Hbud]. apply andb_prop in Ec as [Hok Hnoexp]. apply Z.leb_le in Hbud.
  destruct (len_shape_spec A nZ Esh) as (len & L11 & Hlen & EnZ).
  subst nZ. set (nZ := page_round_up_Z len) in *.
  pose proof HR as [H1 H2 H3 H4 H5 H6 H7 H8 H9 [H10 H10'] H11 H12 H13 H14 H15]. cbn [cfg_ms cfg_model] in *.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 17) 17%uint63 226 H4 eq_refl H17) as R17.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 11) 11%uint63 len H4 eq_refl L11) as R11.
  pose proof (reg_lit ρ _ ms (Z_to_bv 5 12) 12%uint63 3 H4 eq_refl L12) as R12.
  pose proof (xform_sound ρ _ _ (rg ms (Z_to_bv 5 10)) f H11 (H4 (Z_to_bv 5 10)) Ef) as R10.
  destruct (find_ent_spec _ f nZ _ e0 Ee) as [He0 Hhas]. destruct (ent_has_sound ρ _ f nZ e0 H11 Hhas) as [Hlo Hhi].
  destruct (page_round_up_bounds len ltac:(lia)) as [Hb1 Hb2]. fold nZ in Hb1, Hb2.
  assert (HnZ : 0 < nZ < 70368744181760) by lia.
  destruct (expose_parts A f nZ e0 Hok) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8).
  pose proof (lin_al_sound ρ 4096 f ltac:(lia) P4) as Hal.
  pose proof (no_exp_sound e0 _ Hnoexp) as Hnx.
  assert (Hexp : forall z, leval ρ f <= z < leval ρ f + nZ -> ~ in_exp ρ (am_exp (a_model A)) e0 z)
    by (intros z _ [x [Hx [Hxe _]]]; exact (Hnx x Hx Hxe)).
  (* [comment removed for export] *)
  pose proof (gate_of_MR segs fs0 ρ _ model H8 e0 He0 f len Hlen Hlo Hhi Hal (rg ms (Z_to_bv 5 10)) (rg ms (Z_to_bv 5 11)) R10 R11) as G.
  pose proof (gate_addr ρ f (rg ms (Z_to_bv 5 10)) R10) as Eaddr.
  pose proof (gate_fix_n len (rg ms (Z_to_bv 5 11)) R11) as En. fold nZ in En.
  pose proof (gate_n_unsigned ρ f len Hlen (rg ms (Z_to_bv 5 11)) R11) as Un. fold nZ in Un.
  pose proof (MR_ent segs fs0 ρ _ model e0 H8 He0) as Hent. pose proof Hent as (K1 & K2 & K3).
  pose proof (rng_top segs fs0 ρ _ model H8 e0 He0 f nZ Hhi) as Htop. pose proof (alloc_top_lt (m_vmmaps model)) as Hatl.
  assert (PG : prot_gate model (rg ms (Z_to_bv 5 10)) (rg ms (Z_to_bv 5 11))).
  { constructor.
    - exact (fg_len _ _ _ G).
    - exact (fg_al _ _ _ G).
    - rewrite (gate_fix_nZ len (rg ms (Z_to_bv 5 11)) R11), R10. fold nZ. lia.
    - unfold map_contains. apply existsb_exists. exists (ent_val ρ e0). split; [exact (mr_nacov2 segs fs0 ρ _ model H8 e0 He0 P1 Hnx)|].
      pose proof (ent_val_bas ρ e0 Hent) as Eb. pose proof (ent_val_bsz ρ e0 Hent) as Es. unfold bas, bsz in Eb, Es.
      rewrite Eb, Es, Un, R10. apply andb_true_intro. split; apply Z.leb_le; lia.
    - exact (fg_own _ _ _ G). }
  destruct (prot_shape_lit (rg ms (Z_to_bv 5 12)) R12) as [S1 S2].
  set (addr := rg ms (Z_to_bv 5 10)) in *. set (nw := fix_n (rg ms (Z_to_bv 5 11))) in *.
  set (m' := mprotect_model_next model addr nw).
  assert (Wa : bv_unsigned addr = leval ρ f) by exact R10.
  assert (Hused : vm_backing_used m' <= a_budget A + nZ).
  { assert (Hrange : bv_unsigned addr + bv_unsigned nw <= AxAcct.two64) by (rewrite Wa, Un; unfold AxAcct.two64; unfold two_pow_64 in Hatl; lia).
    assert (HSW : forall x, bv_unsigned addr <= x < bv_unsigned addr + bv_unsigned nw -> SW (vm_maps (m_vmmaps model)) x <= 1)
      by (intros x _; apply SW_le_1; exact (mr_pw segs fs0 ρ _ model H8)).
    pose proof (used_prot model addr nw (MR_maps_nowrap segs fs0 ρ _ model H8) (mr_na segs fs0 ρ _ model H8) 1 ltac:(lia) HSW) as X.
    fold m' in X. rewrite Un in X. lia. }
  assert (Hlim : vm_limit (m_vmmaps m') = LIM) by (unfold m'; rewrite prot_vmmaps; exact H10').
  assert (Hbok : mprotect_budget_ok model addr nw = true).
  { unfold mprotect_budget_ok, vm_backing_within_limit. fold m'. apply Z.leb_le. rewrite Hlim. lia. }
  apply (rzc_latch segs cfg ms model w (KT ρ o) H9 H3 Hf He).
  apply (rzc_sys_silent segs cfg (latch ms) model (rg ms (Z_to_bv 5 17)) (KT ρ o) H9 eq_refl).
  - rewrite (check_syscall_226 segs (latch ms) _ _ model R17).
    exact (chk_prot_modeled model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) S1 S2 PG _).
  - intros eff m1 evs Hc. rewrite (check_syscall_226 segs (latch ms) _ _ model R17) in Hc.
    destruct (chk_prot_halted model addr _ _ S1 S2 PG eff m1 evs Hc) as [E1 E2]. split; [exact E1 | rewrite E2; exact H9].
  - exists (mkEffect (Z_to_bv 64 0) [] [(addr, nw)]), m'. split.
    + rewrite (check_syscall_226 segs (latch ms) _ _ model R17).
      exact (chk_prot_grant model addr (rg ms (Z_to_bv 5 11)) (rg ms (Z_to_bv 5 12)) S1 S2 PG Hbok).
    + rewrite (refusal_b_226 segs (latch ms) _ model _ R17). reflexivity.
  - intros eff m1 Hc Hnr. rewrite (check_syscall_226 segs (latch ms) _ _ model R17) in Hc.
    destruct (chk_prot model addr _ _ S1 S2 PG eff m1 [] Hc) as [Hr|(-> & -> & _ & _)].
    + exfalso. specialize (Hnr (family_off_alloc segs cfg (latch ms) _ Hcfg2 ltac:(rewrite R17; cbn; tauto) ltac:(rewrite R17; lia))).
      rewrite (refusal_b_226 segs (latch ms) _ model _ R17) in Hnr.
      change (ret_in_errnos [ENOMEM] (eff_ret eff)) with (errno_ret_in mprotect_errnos (eff_ret eff)) in Hnr. congruence.
    + fold m'. exists m'. split; [exact (materialize_nil m')|]. rewrite adv_zeros.
      set (B := expose_next A (aset (a_regs A) reg_a0 (XL w_zero)) f nZ e0 (a_budget A + nZ)).
      apply (HS B (or_introl eq_refl) ρ); [|exact Ho].
      assert (Hmods : vm_maps (m_vmmaps m') = vm_maps (m_vmmaps model) /\ alloc_top (m_vmmaps m') = alloc_top (m_vmmaps model)
                      /\ vm_noaccess (m_vmmaps m') = maps_subtract (vm_noaccess (m_vmmaps model)) (leval ρ f) (leval ρ f + nZ)).
      { unfold m'. rewrite prot_vmmaps. cbn [vm_maps vm_noaccess alloc_top vm_init_sp]. rewrite Wa, Un. repeat split; reflexivity. }
      destruct Hmods as (M1 & M2 & M3).
      destruct (expose_mem segs fs0 LIM Hlow ρ A ms model HR f nZ e0 Hok He0 HnZ Hb2 Hlo Hhi Hexp m' M1 M2 M3) as (X1 & X2 & X3 & X4 & X5).
      change (fix_n (rg ms (Z_to_bv 5 11))) with nw. rewrite En, Eaddr.
      apply (R_sys_post_B segs fs0 LIM ρ A B ms model m' _ (XL w_zero) _ HR); try reflexivity; try assumption.
      * unfold m'. rewrite En, Eaddr. exact (MR_prot segs fs0 ρ _ model H8 e0 He0 f nZ ltac:(lia) Hlo Hhi (conj Hal ltac:(unfold nZ, page_round_up_Z, page_size; apply Z_mod_mult))).
Qed.

End Main.
