(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsB Od_cpsB Od_hkit0A Od_deldtorA Od_beginB Od_loopB.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Export Od_top_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section Top.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Hypothesis AF : art_facts RT.

Hypothesis HEAD : forall E, od_oka E -> od_shb E -> HLASTP E -> od_head_stmt E.
Hypothesis HEXIT : forall E, od_oka E -> od_head_exit_stmt E.
Hypothesis PLUS : forall E, od_oka E -> od_shb E -> HLASTP E -> od_plus_stmt E.
Hypothesis BEGIN : forall E, od_oka E -> od_shb E -> od_begin_stmt E.
Hypothesis DBL : forall PMc, fdfs_only PMc -> mat_stable PMc -> arm_dbl_cps RT PMc.
Hypothesis SETUP : forall PMc, od_setup_stmt RT LIB PMc.
Hypothesis EXITP : forall PMc, fdfs_only PMc -> mat_stable PMc -> od_exitp_stmt RT LIB PMc.

Theorem fuzz_one_odB : fuzz_one_cps RT LIB.
Proof using AF HEAD HEXIT PLUS BEGIN DBL SETUP EXITP.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 S0C LIB0 IOS ART0 MI0 ST0 LOW LOR SPT SPA SPLE FRM.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  match goal with |- cps bsegs _ ?K0 => set (K := K0) end.

  assert (KFIN : od_fin_k RT LIB PMc K Σ usp lo ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST)).
  { unfold od_fin_k. intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' PR' LIB' LV' FRS' SP' CR'.
    apply (aevt_done RT PMc). intros c Hc. subst K. cbv beta. split.
    - exists Σ'. split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'| exact CR']]]].
      eapply ASTA_conseq; [exact Hc|]. intros ms <-. exists m'. subst tp.
      split; [rewrite ESP; do 16 eexists; reflexivity|]. split; [split; [exact ART'| split; [exact MI'| exact ST']]|].
      split; [rewrite FRS0; exact PR'| exact LIB'].
    - rewrite (asta_eq_fcsr RT Σ' PMc _ c Hc). exact FRM'. }
  eapply cps_conseq; [| intros c [Hc _]; exact Hc| intros c Hc; exact Hc].
  apply (SETUP PMc Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
           FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM); [| exact KFIN].

  intros Σ1 E A cap size IA OC els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs6 xs9 xt3 xt4 xt5 xt6 xF xfc m1
    G R PRE EM0 OUT EUSP ELO EGP SP1 CR1 FRM1.
  pose proof (od_oka_of_rt RT AF Σ1 E m1 G R) as OK. pose proof (od_shb_of_rt RT AF Σ1 E m1 G R) as HG.
  pose proof (od_n_range E (og_s1 _ G)) as NR.
  assert (KFIN1 : od_fin_k RT LIB PMc K Σ (oa_USP E) (o_lo E) ra (o_gp E) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m (rt_credit RT Σ - FUZZ_COST))
    by (rewrite EUSP, ELO, EGP; exact KFIN).

  assert (KX : forall c, rt_credit RT Σ - FUZZ_COST <= c -> od_exit_kc RT PMc Σ1 K E m1 c).
  { intros c Hc. unfold od_exit_kc.
    intros Σ' m0' st vs v88 v144 v152 v240 v312 v336 v352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys3 ys4 ys5 ys6 ys8 ys9 ys11 yt3 yt4 yt5 yt6 yF yfc m2
      R' LV' FRS' SP' CR' FRM' INV'.
    eapply (EXITP PMc FDO MST Σ Σ' K (oa_rebase E m0') m1 m A cap size IA OC els (rt_live RT Σ) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             (rt_credit RT Σ - FUZZ_COST) st vs v88 v144 v152 v240 v312 v336 v352);
      [ exact (od_geo_rebase E m0' G) | exact R' | exact (od_outer_rebase RT LIB Σ1 Σ' E m0' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ OUT LV')
      | reflexivity | rewrite SP'; exact SP1 | lia | exact FRM' | exact INV' | exact KFIN1 ]. }
  apply (aevt_evt RT AF PMc MST).
  eapply (BEGIN E OK HG (fun ms => aevt RT PMc Σ1 K ms)); [exact PRE| exact FRM1| exact EM0| |].
  -
    apply (od_exit_k_of_kc RT PMc Σ1 K E m1 (rt_credit RT Σ - FUZZ_COST) R); [unfold OD_DBL_CREDIT in CR1; lia|].
    apply KX. lia.
  -
    intros HL. unfold od_head_k. intros st v336 v352 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys5 ys6 yt3 yt4 yt5 yt6 yF yfc m2 PRE2 FRM2 INV2.
    apply evt_done.
    destruct PRE2 as [NX|DEAD].
    + eapply (od_loopB RT AF PMc MST HEAD HEXIT PLUS (DBL PMc FDO MST) (Z.to_nat (o_n E + 1)) Σ1 K E m1 od_init st v336 v352);
        [ exact G | exact R | exact HL
        | destruct NX as ((A1 & A2) & _); unfold o_left, od_init in *; cbn [o_pos] in A1; rewrite Z2Nat.id by lia; lia
        | rewrite Z2Nat.id by lia; unfold OD_DBL_CREDIT in *; lia | left; exact NX | exact FRM2 | exact INV2 | ].
      apply KX. rewrite Z2Nat.id by lia. unfold OD_DBL_CREDIT in *. lia.
    + apply (aevt_evt RT AF PMc MST).
      eapply (HEXIT E OK (fun ms => aevt RT PMc Σ1 K ms) st v336 v352);
        [destruct DEAD as (_ & DD & _); lia| exact FRM2| exact INV2|].
      apply (od_exit_k_of_kc RT PMc Σ1 K E m1 (rt_credit RT Σ - FUZZ_COST) R); [unfold OD_DBL_CREDIT in CR1; lia|].
      apply KX. lia.
Qed.

End Top.
