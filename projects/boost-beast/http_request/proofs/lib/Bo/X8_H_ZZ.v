(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require TP_0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac MState Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsIface5 AsIface6 AsIface7 AsIface8 AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2
     AsTRList AXImgKit X8_P_ftab_rep AXFuzz_stmt X8_sct_stmt X8_read_stmt X8_sro_stmt X8_H_stmt X8_H_T0 X8_H_T X8_H_Z
     X8_stream_stmt2 X8_stream_stmt4 X8_S_mi2 X8_S_fbp2 X8_SC4 X8_put_stmt X8_read2 X8_read6 X8_sro X8_H_Y.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import AS_InstDefs BoTop.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Hypothesis H5 : asan_rt_hyps5 H.
  Hypothesis H5x : asan_rt_hyps5x H.
  Hypothesis H6 : asan_rt_hyps6.
  Hypothesis H6b : asan_rt_hyps6b.
  Hypothesis H7 : asan_rt_hyps7 H.
  Hypothesis H8 : asan_rt_hyps8 H.
  Hypothesis ATR : incl TRLIST (as_TR H).
  (* [comment removed for export] *)
  Lemma Y_HREAD : forall MA MR, hread_stmt H MA MR.
  Proof.
    exact (hread_spec H HH (proj1 H5) (proj1 (proj2 H5)) H7 H8 ATR
             (fun MX CX MA R => bput_stmtR_of H MX CX MA R (bput_closed H HH H5 H5x H6 MX CX MA R))).
  Qed.

  (* [comment removed for export] *)
  Lemma Y_SCT : stream_ctor_stmt H.
  Proof. exact (stream_ctor_spec H HH (make_impl_spec H HH) (fb_prepare_spec H HH H7)). Qed.
  (* [comment removed for export] *)
  Lemma Y_SRO : forall MX CX MA MR, sro_stmt H MX CX MA MR.
  Proof. exact (sro_spec H HH Y_HREAD). Qed.

  Lemma afuzz_with_closed : afuzz_stmt_with H (AHStat FT).
  Proof.
    unfold afuzz_stmt_with. intros.
    lazymatch goal with |- as_SR H (afuzz_post _ _ ?ra ?sp ?gp ?tp ?s0 ?s1 ?s2 ?s3 ?s4 ?s5 ?s6 ?s7 ?s8 ?s9 ?s10 ?s11 ?F ?fc ?s ?LB ?LF ?N ?lo ?B ?shi ?m ?mo) ?c =>
      assert (K : as_SR H (hz_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF N lo B shi m mo) c) end.
    { eapply (afuzz_core H HH H5 H6 H6b ATR Y_SCT Y_SRO); try eassumption.
      all: unfold APF_FUZZ, afuzz_cost, hz_afuzz_cost in *; try eassumption. }
    revert K. unfold afuzz_post, hz_post, AXH_X, afuzz_cost, hz_afuzz_cost. intros K. exact K.
  Qed.

  Theorem afuzz_closed_with : afuzz_stmt H.
  Proof.
    exists (AHStat FT). split; [exact (AHStat_local FT FT_local)|]. split; [exact (AHStat_initial FT)| exact afuzz_with_closed].
  Qed.
End HCW.

(* [comment removed for export] *)
Theorem BFUZZ_closed : BFUZZ.
Proof. intros HCEIL H HH H5 H5x H6 H6b H7 H8 ATR. exact (afuzz_closed_with H HH H5 H5x H6 H6b H7 H8 ATR). Qed.

Theorem BCOST_closed : BCOST.
Proof.
  apply ACOST_of_bound. intros HCEIL p. unfold afuzz_cost, AFUZZ_COST_MAX. cbn [as_Cm as_Cf KHp]. unfold ICm, ICf.
  change (13 * 2 ^ 26 + 600000000 <=? 64512) with false. cbv iota. lia.
Qed.
