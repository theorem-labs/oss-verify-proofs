(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import ImageA Tac RzCPS NodesA SysStep FarCall.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit Fz_G_pkit.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow RT_cg.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout PLayout RT_iface RT_iface_pem D_defs D_kit D_agree D_clx R_cache_defs Fz_kit I_ut I_lkit Fz_chk Fz_fkit Fz_G_kit Fz_ckit Fz_env Fz_M_malloc Th_tsd Th_key Th_once Th_mutex Fz_T_lock Fz_T_master1 Fz_I3_gdcw Fz_I3_gdc Fz_I3_fxiw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Import ListNotations.
Open Scope Z_scope.
Notation z64 := (Z_to_bv 64 0) (only parsing).

Section Fxi.
Variable RT : rt_sig.
Variable GOBJ : Z -> Z -> Prop.
Hypothesis AF : art_facts RT.
Hypothesis AFP : art_facts_pem RT GOBJ.
Hypothesis C_GDC : gdc_stmt RT.
(* [comment removed for export] *)
Hypothesis GO_dc : GOBJ 0xb9f580 328.

(* [comment removed for export] *)
Definition FXI_SITES : list (Z * Z) := (SITE_gx_gdc, e_gx) :: (SITE_fx_gx, e_fxi_ex) :: GDC_SITES.
Definition FXI_CALLS : list (Z * Z) := (SITE_gx_gdc, e_gdc) :: (SITE_fx_gx, e_gx) :: GDC_CALLS.

Definition fxi_stmt : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z) (outer : list Z) (lb : byte) (canary : word) (nk j : Z) (sh kold w r oldcb : word) (g1 : byte) (g2 : word) (g1_g2 : word) (g1_g3 : word) (g1_g4 : word) (g1_g5 : word) (g1_g6 : word) (g1_g7 : word) (g1_g8 : word) (g1_g9 : word) (g1_g10 : word) (g1_g11 : word) (g1_g12 : word) (g1_g13 : word) (g1_g14 : word) (g1_g15 : word) (g1_g16 : word) (g1_g17 : word) (g1_g18 : word) (g1_g19 : word) (g1_g20 : word) (g1_g21 : word) (g1_g2_g2 : word) (g1_g5_od : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A -> a0 = z64 -> a1 = Z_to_bv 64 (-1) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> lo + RT_STACK + 0x5c0 <= bv_unsigned sp ->
  cg_ctx (rt_cg RT Σ) e_fxi (bv_unsigned ra :: outer) -> In (bv_unsigned ra, e_fxi_ex) (cg_call (rt_cg RT Σ)) -> uw_chain m sp s0 outer ->
  cg_has (rt_cg RT Σ) FXI_SITES FXI_CALLS ->
  (length (rt_frames RT Σ) + 1 < FRAMES_MAX)%nat -> Z.of_nat (length (rt_live RT Σ)) + 124 <= LIVE_MAX -> GDC_COST <= rt_credit RT Σ ->
  Forall (fun x => 0 < snd x) (rt_live RT Σ) ->
  cl_env m lb canary ->
  rw_cells asegs m 0xb9f740 [C4 z64] -> rw_cells asegs m 0xb9f780 [C4 z64] -> rw_cells asegs m 0xb9f720 [C4 kold] -> rw_cells asegs m 0xb9f760 [C4 r] ->
  rw_cells asegs m NEXT_KEY [C4 (Z_to_bv 64 nk)] -> 1 <= nk < 127 -> rw_cells asegs m KEY_LOCK [C4 z64; C4 z64; C4 sh] ->
  rw_cells asegs m (KEYS + 8 * j) [C8 z64] -> ro_cells asegs m (KEYS + 8 * nk) [C8 w] ->
  ((j = nk /\ w = z64) \/ (j = (nk + 1) mod 128 /\ bv_unsigned w <> 0)) ->
  rw_cells asegs m (TSD_MAIN + 8 * j) [C8 z64] -> rw_cells asegs m (TP_A + -96) [C8 oldcb] -> rw_cells asegs m 0xb9f5f0 [C8 z64] ->
  rw_cells asegs m 0xb9f560 [C1 g1] ->
  rw_cells asegs m 0xb9f7a0 [C4 g2] ->
  rw_cells asegs m 0xb9f580 [C8 g1_g2] ->
  rw_cells asegs m 0xb9f628 [C8 g1_g3] ->
  rw_cells asegs m 0xb9f630 [C8 g1_g4] ->
  rw_cells asegs m 0xb9f638 [C8 g1_g5] ->
  rw_cells asegs m 0xb9f640 [C8 g1_g6] ->
  rw_cells asegs m 0xb9f648 [C8 g1_g7] ->
  rw_cells asegs m 0xb9f650 [C8 g1_g8] ->
  rw_cells asegs m 0xb9f658 [C8 g1_g9] ->
  rw_cells asegs m 0xb9f660 [C8 g1_g10] ->
  rw_cells asegs m 0xb9f668 [C8 g1_g11] ->
  rw_cells asegs m 0xb9f670 [C8 g1_g12] ->
  rw_cells asegs m 0xb9f678 [C8 g1_g13] ->
  rw_cells asegs m 0xb9f680 [C8 g1_g14] ->
  rw_cells asegs m 0xb9f688 [C8 g1_g15] ->
  rw_cells asegs m 0xb9f690 [C8 g1_g16] ->
  rw_cells asegs m 0xb9f698 [C8 g1_g17] ->
  rw_cells asegs m 0xb9f6a0 [C8 g1_g18] ->
  rw_cells asegs m 0xb9f6a8 [C8 g1_g19] ->
  rw_cells asegs m 0xb9f6b0 [C8 g1_g20] ->
  rw_cells asegs m 0xb9f6b8 [C8 g1_g21] ->
  rw_cells asegs m 0xb9f588 [C8 g1_g2_g2] ->
  rw_cells asegs m 0xb9f200 [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m 0xb9f2a0 [C8 g1_g5_od] ->
  rw_cells asegs m 0xb9f2c0 [C4 (Z_to_bv 64 2)] ->
  rw_cells asegs m 0xb9f2e0 [C4 (Z_to_bv 64 1)] ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fxi m)))
    (fun c => exists (Σ' : rts RT) (lk : Z),
       ASTA RT Σ' PMc (fun ms => exists (m' : mem), ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 0) m' ms
           /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
           /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) (GDC_W j) m m'
           /\ cl_env m' (Z_to_bv 8 1) canary
           /\ rw_cells asegs m' 0xb9f740 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' 0xb9f780 [C4 (Z_to_bv 64 2)]
           /\ rw_cells asegs m' 0xb9f720 [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' 0xb9f760 [C4 (Z_to_bv 64 1)]
           /\ rw_cells asegs m' NEXT_KEY [C4 (Z_to_bv 64 j)] /\ rw_cells asegs m' KEY_LOCK [C4 z64; C4 z64; C4 sh] /\ rw_cells asegs m' (KEYS + 8 * j) [C8 (Z_to_bv 64 NODTOR)]
           /\ rw_cells asegs m' (TSD_MAIN + 8 * j) [C8 z64] /\ rw_cells asegs m' (TP_A + -96) [C8 oldcb] /\ rw_cells asegs m' 0xb9f5f0 [C8 z64]
           /\ In (lk, 40) (rt_live RT Σ') /\ rw_cells asegs m' 0xb9f588 [C8 (Z_to_bv 64 lk)] /\ rw_cells asegs m' lk (mutex_cells (Z_to_bv 64 0) (Z_to_bv 64 0))
           /\ rw_cells asegs m' 0xb9f7a0 [C4 (Z_to_bv 64 1)] /\ rw_cells asegs m' 0xb9f560 [C1 (Z_to_bv 8 1)]
           /\ rw_cells asegs m' 0xb9f200 [C1 (Z_to_bv 8 0)] /\ rw_cells asegs m' 0xb9f2c0 [C4 (Z_to_bv 64 2)] /\ rw_cells asegs m' 0xb9f2e0 [C4 (Z_to_bv 64 1)]) c
       /\ dc_blocks_ok RT Σ Σ' lk /\ 1 <= j < 128 /\ lk mod 16 = 0
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - GDC_COST /\ rt_cg RT Σ' = rt_cg RT Σ).

Theorem fxi_cps : fxi_stmt.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo outer lb canary nk j sh kold w r oldcb g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
    FDO MST -> -> -> ART0 MI0 CALL HSTK CTX INRA UWC CGH Hfr Hlen Hcr POS0 ENV O1 O2 KC RC NK HNK KL KJ PROBE CASE TSDJ CBC IP12 X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15 X16 X17 X18 X19 X20 X21 X22 X23 X24 X25 X26.
  intros T c HA Hk. pose proof CALL as (ST & LOW & LOR & SPT & SPA).
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W. pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. set (usp := bv_unsigned sp) in *.
  assert (NUM : rt_sp0 RT Σ - STACK_WIN <= usp - 176 /\ 0x10007fff8000 <= lo /\ usp <= USTACK_TOP /\ usp <= 2^47) by (unfold RT_STACK, STACK_WIN, USTACK_TOP in *; lia).
  set (usp1 := usp + -80). set (usp2 := usp + -64).
  cl_eu usp (-80) EU1. cl_eu usp (-64) EU2. fold usp1 in EU1. fold usp2 in EU2.
  destruct (af_client_consts RT AF Σ m ART0) as (_ & SHC & _ & UAR & UT).
  (* [comment removed for export] *)
  pose proof (fxi_w0 ra sp gp (Z_to_bv 64 TP_A) t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
                ST ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) UT SHC MI0) as W0.
  cl_lift W0 HA c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (j8 & m1 & -> & MU1 & WM1 & MI1 & REC1 & FR1 & ST1) & Hc1'). clear Hc1.
  fold usp in MU1, REC1, FR1, ST1, Hc1'. fold usp1 in REC1, ST1, Hc1'. fold usp2 in FR1, Hc1'.
  assert (MU1' : munch ([] ++ [(usp - 80, usp)]) m m1) by exact MU1.
  pose proof (cl_seg_ART RT AF Σ m m1 usp 80 [] ART0 ltac:(clear - NUM; lia) ltac:(clear - NUM; lia) MU1' ltac:(intros x Hx; exfalso; apply Hx; exact I) WM1) as ART1.
  pose proof (cl_seg_pres RT AF Σ m m1 usp 80 [] ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) MU1') as PR1.
  assert (AG1 : agree_on (fun x => usp <= x < USTACK_TOP) m m1) by (intros a Ha; apply PR1; [left; exact Ha | exact I]).
  assert (STAT1 : forall a cs, rw_cells asegs m a cs -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 -> rw_cells asegs m1 a cs).
  { intros a cs H R. apply (wg_keep_seg _ m m1 _ _ H MU1 WM1). intros x Hx. cbn [app outside]. clear - Hx R NUM HSTK. unfold RT_STACK in *. lia. }
  assert (PROBE1 : ro_cells asegs m1 (KEYS + 8 * nk) [C8 w]).
  { apply (wg_keep_seg_ro _ m m1 _ _ PROBE MU1). intros x Hx. cbn [app outside cells_size csize Nat.add] in Hx |- *. clear - Hx HNK NUM HSTK. unfold RT_STACK in *. lia. }
  assert (HJ : 0 <= j < 128) by (destruct CASE as [[-> _] | [-> _]]; [clear - HNK; lia | clear - HNK; pose proof (Z.mod_pos_bound (nk + 1) 128 ltac:(lia)); lia]).
  pose proof (STAT1 _ _ O1 ltac:(cbn; clear; lia)) as O1_1. pose proof (STAT1 _ _ O2 ltac:(cbn; clear; lia)) as O2_1.
  pose proof (STAT1 _ _ KC ltac:(cbn; clear; lia)) as KC1. pose proof (STAT1 _ _ RC ltac:(cbn; clear; lia)) as RC1.
  pose proof (STAT1 _ _ NK ltac:(cbn; clear; lia)) as NK1. pose proof (STAT1 _ _ KL ltac:(cbn; clear; lia)) as KL1.
  pose proof (STAT1 _ _ KJ ltac:(cbn; clear - HJ; lia)) as KJ1. pose proof (STAT1 _ _ TSDJ ltac:(cbn; clear - HJ; lia)) as TSDJ1.
  pose proof (STAT1 _ _ CBC ltac:(cbn; clear; lia)) as CBC1. pose proof (STAT1 _ _ IP12 ltac:(cbn; clear; lia)) as IP12_1.
  pose proof (STAT1 _ _ X0 ltac:(cbn; clear; lia)) as X0_1. pose proof (STAT1 _ _ X1 ltac:(cbn; clear; lia)) as X1_1. pose proof (STAT1 _ _ X2 ltac:(cbn; clear; lia)) as X2_1.
  pose proof (STAT1 _ _ X3 ltac:(cbn; clear; lia)) as X3_1. pose proof (STAT1 _ _ X4 ltac:(cbn; clear; lia)) as X4_1. pose proof (STAT1 _ _ X5 ltac:(cbn; clear; lia)) as X5_1.
  pose proof (STAT1 _ _ X6 ltac:(cbn; clear; lia)) as X6_1. pose proof (STAT1 _ _ X7 ltac:(cbn; clear; lia)) as X7_1. pose proof (STAT1 _ _ X8 ltac:(cbn; clear; lia)) as X8_1.
  pose proof (STAT1 _ _ X9 ltac:(cbn; clear; lia)) as X9_1. pose proof (STAT1 _ _ X10 ltac:(cbn; clear; lia)) as X10_1. pose proof (STAT1 _ _ X11 ltac:(cbn; clear; lia)) as X11_1.
  pose proof (STAT1 _ _ X12 ltac:(cbn; clear; lia)) as X12_1. pose proof (STAT1 _ _ X13 ltac:(cbn; clear; lia)) as X13_1. pose proof (STAT1 _ _ X14 ltac:(cbn; clear; lia)) as X14_1.
  pose proof (STAT1 _ _ X15 ltac:(cbn; clear; lia)) as X15_1. pose proof (STAT1 _ _ X16 ltac:(cbn; clear; lia)) as X16_1. pose proof (STAT1 _ _ X17 ltac:(cbn; clear; lia)) as X17_1.
  pose proof (STAT1 _ _ X18 ltac:(cbn; clear; lia)) as X18_1. pose proof (STAT1 _ _ X19 ltac:(cbn; clear; lia)) as X19_1. pose proof (STAT1 _ _ X20 ltac:(cbn; clear; lia)) as X20_1.
  pose proof (STAT1 _ _ X21 ltac:(cbn; clear; lia)) as X21_1. pose proof (STAT1 _ _ X22 ltac:(cbn; clear; lia)) as X22_1. pose proof (STAT1 _ _ X23 ltac:(cbn; clear; lia)) as X23_1.
  pose proof (STAT1 _ _ X24 ltac:(cbn; clear; lia)) as X24_1. pose proof (STAT1 _ _ X25 ltac:(cbn; clear; lia)) as X25_1. pose proof (STAT1 _ _ X26 ltac:(cbn; clear; lia)) as X26_1.
  pose proof (cl_env_seg _ m m1 _ canary ENV MU1 ltac:(first [solve [clear - NUM HSTK; unfold RT_STACK in *; cl_fp_lia] | cl_fp_lia])) as ENV1.
  (* [comment removed for export] *)
  assert (CTX' : cg_ctx (rt_cg RT Σ) e_fxi_ex (bv_unsigned ra :: outer)) by (split; [exact INRA | exact (proj2 CTX)]).
  destruct (cl_chain_call (rt_cg RT Σ) e_fxi_ex e_gx SITE_fx_gx m m1 ra s0 sp (Z_to_bv 64 usp2) outer CTX'
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWC AG1
              ltac:(fold usp; replace (usp - 16) with (usp2 + Z.of_nat (cells_size [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1])) by (unfold usp2; cbn [cells_size csize Nat.add]; lia);
                    exact (rw_cells_skip m1 usp2 [CB 8 j8; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra] FR1))
              ltac:(rewrite EU2; fold usp; unfold usp2; lia) SPT) as (CTXc1 & UWCc1).
  destruct (cl_chain_call (rt_cg RT Σ) e_gx e_gdc SITE_gx_gdc m1 m1 (Z_to_bv 64 SITE_fx_gx) sp (Z_to_bv 64 usp2) (Z_to_bv 64 usp1) (bv_unsigned ra :: outer)
              ltac:(rewrite (unsigned_lit SITE_fx_gx) by (unfold SITE_fx_gx; clear; lia); exact CTXc1)
              ltac:(apply (proj1 CGH); wp_in_lit) ltac:(apply (proj2 CGH); wp_in_lit) UWCc1 ltac:(intros a Ha; reflexivity)
              ltac:(rewrite EU2; replace (usp2 - 16) with usp1 by (unfold usp1, usp2; lia); exact REC1)
              ltac:(rewrite EU1, EU2; unfold usp1, usp2; lia) ltac:(rewrite EU2; unfold usp2; clear - SPT; fold usp in SPT; lia)) as (CTXc2 & UWCc2).
  (* [comment removed for export] *)
  apply (C_GDC Σ PMc (Z_to_bv 64 SITE_gx_gdc) (Z_to_bv 64 usp1) gp (Z_to_bv 64 TP_A) t0 t1 t2 (Z_to_bv 64 usp2) s1 (Z_to_bv 64 0) (Z_to_bv 64 g_shadow_memory_dynamic_address) (Z_to_bv 64 (-1))
           a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 SHB) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1 lo (SITE_fx_gx :: bv_unsigned ra :: outer) lb canary
           nk j sh kold w r oldcb g1 g2 g1_g2 g1_g3 g1_g4 g1_g5 g1_g6 g1_g7 g1_g8 g1_g9 g1_g10 g1_g11 g1_g12 g1_g13 g1_g14 g1_g15 g1_g16 g1_g17 g1_g18 g1_g19 g1_g20 g1_g21 g1_g2_g2 g1_g5_od
           FDO MST eq_refl ART1 MI1).
  { fold usp in SPA. cl_call_ok EU1 ST1 LOW SPA 5. }
  { rewrite EU1. clear - HSTK. unfold usp1, RT_STACK in *. lia. }
  { rewrite (unsigned_lit SITE_gx_gdc) by (unfold SITE_gx_gdc; clear; lia). exact CTXc2. }
  { exact UWCc2. }
  { apply (cg_has_weaken _ _ _ _ _ CGH); vm_compute; reflexivity. }
  { exact Hfr. }
  { exact Hlen. }
  { exact Hcr. }
  { exact POS0. }
  { exact ENV1. }
  { exact O1_1. } { exact O2_1. } { exact KC1. } { exact RC1. } { exact NK1. } { exact HNK. } { exact KL1. } { exact KJ1. } { exact PROBE1. } { exact CASE. }
  { exact TSDJ1. } { exact CBC1. } { exact IP12_1. }
  { exact X0_1. } { exact X1_1. } { exact X2_1. } { exact X3_1. } { exact X4_1. } { exact X5_1. } { exact X6_1. } { exact X7_1. } { exact X8_1. } { exact X9_1. }
  { exact X10_1. } { exact X11_1. } { exact X12_1. } { exact X13_1. } { exact X14_1. } { exact X15_1. } { exact X16_1. } { exact X17_1. } { exact X18_1. } { exact X19_1. }
  { exact X20_1. } { exact X21_1. } { exact X22_1. } { exact X23_1. } { exact X24_1. } { exact X25_1. } { exact X26_1. }
  { exact Hc1'. }
  clear Hc1'. intros c2 (Σ1 & lk & Hc2 & DCB & HJ1 & LK16 & FRS1 & SP1 & CR1 & CG1).
  destruct (ASTA_unpack RT Σ1 _ _ c2 Hc2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & ST2) & PRES2 & ENV2 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & INlk & LKP2 & MC2 & D11 & D12 & D13 & D14 & D15) & Hc2'). clear Hc2.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
  rewrite EU1 in ST2, PRES2. rewrite (ret_pc_even SITE_gx_gdc) in Hc2' by (unfold SITE_gx_gdc; lia).
  (* [comment removed for export] *)
  assert (STK2 : forall a cs, rw_cells asegs m1 a cs -> usp1 <= a -> a + Z.of_nat (cells_size cs) <= USTACK_TOP -> rw_cells asegs m2 a cs).
  { intros a cs H H1 H2. apply (rw_cells_agree_nw asegs m1 m2 _ _ H). intros x Hx. apply PRES2; [left; clear - H1 H2 Hx; lia|]. unfold GDC_W. cbn [app outside]. unfold G_ALLOW_CUST. clear - H1 Hx NUM HSTK HJ. unfold usp1, RT_STACK in *. repeat (split; [lia|]). exact I. }
  pose proof (STK2 _ _ REC1 ltac:(clear; unfold usp1; lia) ltac:(cbn; clear - NUM; unfold usp1, USTACK_TOP in *; lia)) as REC2.
  pose proof (STK2 _ _ FR1 ltac:(clear; unfold usp1, usp2; lia) ltac:(cbn; clear - NUM; unfold usp2, USTACK_TOP in *; lia)) as FR2.
  destruct (af_client_consts RT AF Σ1 m2 ART2) as (_ & SHC2 & _ & _ & UT2).
  pose proof (afp_gsh_byte RT GOBJ AFP Σ1 m2 0xb9f580 328 0xb9f588 ART2 GO_dc ltac:(clear; lia) ltac:(clear; lia) ltac:(reflexivity)) as GB2.
  pose proof (af_live_range RT AF Σ1 m2 lk 40 ART2 INlk) as (_ & LKLO & _). rewrite SP1 in LKLO.
  pose proof (afp_live_hi RT GOBJ AFP Σ1 m2 lk 40 ART2 INlk ltac:(clear; lia)) as LKH.
  (* [comment removed for export] *)
  pose proof (fxi_w1 sp gp (Z_to_bv 64 TP_A) u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 s2 s3 s4 F2 fc2 m2 lo lk j8) as W1.
  fold usp in W1. fold usp1 in W1. fold usp2 in W1.
  specialize (W1 ST2 ltac:(clear - NUM; lia) ltac:(clear - HSTK; unfold RT_STACK in *; lia) ltac:(clear - NUM; lia) UT2 SHC2 REC2 FR2 GB2 LKP2 MC2 LKH
                 ltac:(clear - LKLO LOW; lia) LK16 MI2).
  cl_lift W1 Hc2' c3 Hc3.
  destruct (ASTA_unpack RT Σ1 _ _ c3 Hc3) as (ms3 & (a1' & a2' & a3' & a4' & a5' & m3 & -> & MU3 & WM3 & MI3 & MC3 & ST3) & Hc3'). clear Hc3.
  fold usp in MU3, ST3, Hc3'.
  (* [comment removed for export] *)
  assert (MU3' : munch ([(lk + 4, lk + 8)] ++ [(usp - 176, usp)]) m2 m3) by (eapply munch_weaken; [| exact MU3]; unfold sub_fp; cbn [outside app]; intros; lia).
  assert (ART3 : ART RT Σ1 m3).
  { apply (wg_seg_ART RT AF Σ1 m2 m3 usp 176 [(lk + 4, lk + 8)] ART2 ltac:(rewrite SP1; clear - NUM; lia) ltac:(clear - NUM; lia) MU3'); [| exact WM3].
    intros x Hx. right. exists lk, 40. split; [exact INlk|]. cbn [outside] in Hx. clear - Hx. lia. }
  assert (STA3 : forall a cs, rw_cells asegs m2 a cs -> a + Z.of_nat (cells_size cs) <= 0x10007fff8000 -> rw_cells asegs m3 a cs).
  { intros a cs H R. apply (rw_cells_agree_nw asegs m2 m3 _ _ H). intros x Hx. apply MU3. cbn [app outside]. clear - R Hx NUM HSTK LKH. unfold RT_STACK in *. lia. }
  destruct DCB as (news & LV1 & LEN1 & FA1 & INN).
  apply Hk. exists Σ1, lk.
  split; [| split; [exists news; split; [exact LV1 | split; [exact LEN1 | split; [exact FA1 | exact INN]]] | split; [exact HJ1 | split; [exact LK16 | split; [exact FRS1 | split; [exact SP1 | split; [exact CR1 | exact CG1]]]]]]].
  eapply ASTA_conseq; [exact Hc3'|]. intros ms <-. exists m3.
  split; [exists u0, u1, u2, a1', a2', a3', a4', a5', b6, b7, u3, u4, u5, u6, F2, fc2; reflexivity|].
  split; [split; [exact ART3 | split; [exact MI3 | exact ST3]]|].
  split.
  { intros a Ha Ho.
    pose proof (cl_split RT AF Σ m usp 176 _ ART0 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as SPL.
    pose proof (wg_newchunk_apart RT AF Σ Σ1 m2 news lk 40 usp (bv_unsigned a) ART2 LV1 INN FRS1 SP1 ltac:(clear - NUM; lia) ltac:(clear; lia) Ha) as NLK.
    rewrite (MU3 a ltac:(clear - SPL NLK; cbn [outside]; lia)).
    assert (A2 : aclient (rt_live RT Σ) (rt_frames RT Σ) usp1 (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto | auto | clear; unfold usp1; lia]).
    rewrite (PRES2 a A2 Ho).
    exact (PR1 a Ha I). }
  split; [exact (cl_env_seg _ m2 m3 _ canary ENV2 MU3 ltac:(first [solve [clear - NUM HSTK LKH; unfold RT_STACK in *; cl_fp_lia] | cl_fp_lia]))|].
  split; [exact (STA3 _ _ D1 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D2 ltac:(cbn; clear; lia))|].
  split; [exact (STA3 _ _ D3 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D4 ltac:(cbn; clear; lia))|].
  split; [exact (STA3 _ _ D5 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D6 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D7 ltac:(cbn; clear - HJ; lia))|].
  split; [exact (STA3 _ _ D8 ltac:(cbn; clear - HJ; lia))|]. split; [exact (STA3 _ _ D9 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D10 ltac:(cbn; clear; lia))|].
  split; [exact INlk|]. split; [exact (STA3 _ _ LKP2 ltac:(cbn; clear; lia))|]. split; [exact MC3|].
  split; [exact (STA3 _ _ D11 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D12 ltac:(cbn; clear; lia))|].
  split; [exact (STA3 _ _ D13 ltac:(cbn; clear; lia))|]. split; [exact (STA3 _ _ D14 ltac:(cbn; clear; lia)) | exact (STA3 _ _ D15 ltac:(cbn; clear; lia))].
Qed.
End Fxi.
