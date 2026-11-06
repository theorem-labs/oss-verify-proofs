(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require T_Ubs2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2L Require T_Ubs2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require T_Ubs2U.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require T_Ubs2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require B_01.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_02 B_03 B_07 B_08 B_09.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5 Ubs_u_6 Ubs_u_7 Ubs_u_8 Ubs_u_9 Ubs_u_10 Ubs_u_11 Ubs_u_12 Ubs_u_13.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.
Module C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.
Module C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.
Module C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.
Module C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.
Module C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.
Module C_UW_52944_15e9e_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_15e9e_w6_r13_pP_L0.
Module C_UW_52944_15e9e_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_15e9e_w7_r14_pv_L0.
Module C_UW_52944_45f12_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_45f12_w6_r13_pP_L0.
Module C_UW_52944_45f12_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_45f12_w7_r14_pv_L0.
Module C_UW_52944_853c2_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_853c2_w6_r13_pP_L0.
Module C_UW_52944_853c2_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_853c2_w7_r14_pv_L0.
Module C_UW_52944_bb428_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_bb428_w6_r13_pP_L0.
Module C_UW_52944_bb428_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_bb428_w7_r14_pv_L0.
Module C_UW_52944_bb715_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_bb715_w6_r13_pP_L0.
Module C_UW_52944_bb715_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_bb715_w7_r14_pv_L0.
Module C_UW_52944_c50a9_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_UW_52944_c50a9_w6_r13_pP_L0.
Module C_UW_52944_c50a9_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_UW_52944_c50a9_w7_r14_pv_L0.
Module C_UW_52944_cd178_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_UW_52944_cd178_w6_r13_pP_L0.
Module C_UW_52944_cd178_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_UW_52944_cd178_w7_r14_pv_L0.
Module C_XA_52944_15e9e_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_15e9e_blk_w7_r14_L0.
Module C_XA_52944_15e9e_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_15e9e_p682f0_w6_r13_pP.
Module C_XA_52944_45f12_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_45f12_blk_w7_r14_L0.
Module C_XA_52944_45f12_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_45f12_p682f0_w6_r13_pP.
Module C_XA_52944_853c2_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_853c2_blk_w7_r14_L0.
Module C_XA_52944_853c2_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_853c2_p682f0_w6_r13_pP.
Module C_XA_52944_bb428_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_bb428_blk_w7_r14_L0.
Module C_XA_52944_bb428_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_bb428_p682f0_w6_r13_pP.
Module C_XA_52944_bb715_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_bb715_blk_w7_r14_L0.
Module C_XA_52944_bb715_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_bb715_p682f0_w6_r13_pP.
Module C_XA_52944_c50a9_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_c50a9_blk_w7_r14_L0.
Module C_XA_52944_c50a9_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_c50a9_p682f0_w6_r13_pP.
Module C_XA_52944_cd178_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_cd178_blk_w7_r14_L0.
Module C_XA_52944_cd178_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_cd178_p682f0_w6_r13_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4 Ubs_u_5.LibRunUbs_u_5 Ubs_u_6.LibRunUbs_u_6 Ubs_u_7.LibRunUbs_u_7 Ubs_u_8.LibRunUbs_u_8 Ubs_u_9.LibRunUbs_u_9 Ubs_u_10.LibRunUbs_u_10 Ubs_u_11.LibRunUbs_u_11 Ubs_u_12.LibRunUbs_u_12 Ubs_u_13.LibRunUbs_u_13.

Module LibRunUbs_u_14.
Lemma LN_TUE_T_UW_52944_45f12_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_45f12_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_45f12_w7_r14_pv_L0.CTX C_UW_52944_45f12_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_45f12_w7_r14_pv_L0) C_UW_52944_45f12_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_45f12_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_45f12_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_45f12_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_45f12_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_45f12_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_45f12_blk_w7_r14_L0.CTX C_XA_52944_45f12_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_45f12_blk_w7_r14_L0) C_XA_52944_45f12_blk_w7_r14_L0.OBLS [(375%uint63, T_Ubs2UE.T_UW_52944_45f12_w7_r14_pv_L0)] C_XA_52944_45f12_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_45f12_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_45f12_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_45f12_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_45f12_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_45f12_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_45f12_w6_r13_pP_L0.CTX C_UW_52944_45f12_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_45f12_w6_r13_pP_L0) C_UW_52944_45f12_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_45f12_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_45f12_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_45f12_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_45f12_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_45f12_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_45f12_p682f0_w6_r13_pP.CTX C_XA_52944_45f12_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_45f12_p682f0_w6_r13_pP) C_XA_52944_45f12_p682f0_w6_r13_pP.OBLS [(374%uint63, T_Ubs2UE.T_UW_52944_45f12_w6_r13_pP_L0)] C_XA_52944_45f12_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_45f12_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_45f12_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_45f12_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e) C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.OBLS [(202%uint63, T_Ubs2UE.T_XA_52944_45f12_blk_w7_r14_L0); (203%uint63, T_Ubs2UE.T_XA_52944_45f12_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f5b0f5e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_45f12_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_45f12_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.CTX C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.OBLS [(278%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e)] C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f5b0f5e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f5b0f5e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_bb715_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_bb715_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_bb715_w7_r14_pv_L0.CTX C_UW_52944_bb715_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_bb715_w7_r14_pv_L0) C_UW_52944_bb715_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_bb715_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_bb715_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_bb715_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_bb715_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_bb715_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_bb715_blk_w7_r14_L0.CTX C_XA_52944_bb715_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_bb715_blk_w7_r14_L0) C_XA_52944_bb715_blk_w7_r14_L0.OBLS [(395%uint63, T_Ubs2UE.T_UW_52944_bb715_w7_r14_pv_L0)] C_XA_52944_bb715_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_bb715_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_bb715_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_bb715_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_bb715_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_bb715_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_bb715_w6_r13_pP_L0.CTX C_UW_52944_bb715_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_bb715_w6_r13_pP_L0) C_UW_52944_bb715_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_bb715_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_bb715_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_bb715_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_bb715_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_bb715_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_bb715_p682f0_w6_r13_pP.CTX C_XA_52944_bb715_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_bb715_p682f0_w6_r13_pP) C_XA_52944_bb715_p682f0_w6_r13_pP.OBLS [(394%uint63, T_Ubs2UE.T_UW_52944_bb715_w6_r13_pP_L0)] C_XA_52944_bb715_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_bb715_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_bb715_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_bb715_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee) C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.OBLS [(222%uint63, T_Ubs2UE.T_XA_52944_bb715_blk_w7_r14_L0); (223%uint63, T_Ubs2UE.T_XA_52944_bb715_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f076dee.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_bb715_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_bb715_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.CTX C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.OBLS [(282%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee)] C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f076dee.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f076dee _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_15e9e_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_15e9e_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_15e9e_w7_r14_pv_L0.CTX C_UW_52944_15e9e_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_15e9e_w7_r14_pv_L0) C_UW_52944_15e9e_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_15e9e_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_15e9e_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_15e9e_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_15e9e_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_15e9e_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_15e9e_blk_w7_r14_L0.CTX C_XA_52944_15e9e_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_15e9e_blk_w7_r14_L0) C_XA_52944_15e9e_blk_w7_r14_L0.OBLS [(371%uint63, T_Ubs2UE.T_UW_52944_15e9e_w7_r14_pv_L0)] C_XA_52944_15e9e_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_15e9e_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_15e9e_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_15e9e_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_15e9e_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_15e9e_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_15e9e_w6_r13_pP_L0.CTX C_UW_52944_15e9e_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_15e9e_w6_r13_pP_L0) C_UW_52944_15e9e_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_15e9e_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_15e9e_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_15e9e_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_15e9e_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_15e9e_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_15e9e_p682f0_w6_r13_pP.CTX C_XA_52944_15e9e_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_15e9e_p682f0_w6_r13_pP) C_XA_52944_15e9e_p682f0_w6_r13_pP.OBLS [(370%uint63, T_Ubs2UE.T_UW_52944_15e9e_w6_r13_pP_L0)] C_XA_52944_15e9e_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_15e9e_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_15e9e_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_15e9e_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa) C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.OBLS [(198%uint63, T_Ubs2UE.T_XA_52944_15e9e_blk_w7_r14_L0); (199%uint63, T_Ubs2UE.T_XA_52944_15e9e_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f03adaa.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_15e9e_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_15e9e_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.CTX C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.OBLS [(285%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa)] C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f03adaa.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f03adaa _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_cd178_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_cd178_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_cd178_w7_r14_pv_L0.CTX C_UW_52944_cd178_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_cd178_w7_r14_pv_L0) C_UW_52944_cd178_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_cd178_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_cd178_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_cd178_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_cd178_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_cd178_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_cd178_blk_w7_r14_L0.CTX C_XA_52944_cd178_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_cd178_blk_w7_r14_L0) C_XA_52944_cd178_blk_w7_r14_L0.OBLS [(403%uint63, T_Ubs2UE.T_UW_52944_cd178_w7_r14_pv_L0)] C_XA_52944_cd178_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_cd178_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_cd178_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_cd178_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_cd178_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_cd178_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_cd178_w6_r13_pP_L0.CTX C_UW_52944_cd178_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_cd178_w6_r13_pP_L0) C_UW_52944_cd178_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_cd178_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_cd178_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_cd178_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_cd178_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_cd178_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_cd178_p682f0_w6_r13_pP.CTX C_XA_52944_cd178_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_cd178_p682f0_w6_r13_pP) C_XA_52944_cd178_p682f0_w6_r13_pP.OBLS [(402%uint63, T_Ubs2UE.T_UW_52944_cd178_w6_r13_pP_L0)] C_XA_52944_cd178_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_cd178_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_cd178_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_cd178_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f) C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.OBLS [(230%uint63, T_Ubs2UE.T_XA_52944_cd178_blk_w7_r14_L0); (231%uint63, T_Ubs2UE.T_XA_52944_cd178_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f6e7a6f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_cd178_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_cd178_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.CTX C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.OBLS [(286%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f)] C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f6e7a6f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f6e7a6f _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_bb428_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_bb428_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_bb428_w7_r14_pv_L0.CTX C_UW_52944_bb428_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_bb428_w7_r14_pv_L0) C_UW_52944_bb428_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_bb428_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_bb428_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_bb428_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_bb428_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_bb428_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_bb428_blk_w7_r14_L0.CTX C_XA_52944_bb428_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_bb428_blk_w7_r14_L0) C_XA_52944_bb428_blk_w7_r14_L0.OBLS [(393%uint63, T_Ubs2UE.T_UW_52944_bb428_w7_r14_pv_L0)] C_XA_52944_bb428_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_bb428_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_bb428_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_bb428_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_bb428_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_bb428_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_bb428_w6_r13_pP_L0.CTX C_UW_52944_bb428_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_bb428_w6_r13_pP_L0) C_UW_52944_bb428_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_bb428_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_bb428_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_bb428_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_bb428_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_bb428_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_bb428_p682f0_w6_r13_pP.CTX C_XA_52944_bb428_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_bb428_p682f0_w6_r13_pP) C_XA_52944_bb428_p682f0_w6_r13_pP.OBLS [(392%uint63, T_Ubs2UE.T_UW_52944_bb428_w6_r13_pP_L0)] C_XA_52944_bb428_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_bb428_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_bb428_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_bb428_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338) C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.OBLS [(220%uint63, T_Ubs2UE.T_XA_52944_bb428_blk_w7_r14_L0); (221%uint63, T_Ubs2UE.T_XA_52944_bb428_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f8d1338.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_bb428_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_bb428_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.CTX C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.OBLS [(287%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338)] C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f8d1338.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f8d1338 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_853c2_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_853c2_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_853c2_w7_r14_pv_L0.CTX C_UW_52944_853c2_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_853c2_w7_r14_pv_L0) C_UW_52944_853c2_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_853c2_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_853c2_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_853c2_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_853c2_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_853c2_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_853c2_blk_w7_r14_L0.CTX C_XA_52944_853c2_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_853c2_blk_w7_r14_L0) C_XA_52944_853c2_blk_w7_r14_L0.OBLS [(387%uint63, T_Ubs2UE.T_UW_52944_853c2_w7_r14_pv_L0)] C_XA_52944_853c2_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_853c2_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_853c2_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_853c2_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_853c2_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_853c2_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_853c2_w6_r13_pP_L0.CTX C_UW_52944_853c2_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_853c2_w6_r13_pP_L0) C_UW_52944_853c2_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_853c2_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_853c2_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_853c2_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_853c2_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_853c2_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_853c2_p682f0_w6_r13_pP.CTX C_XA_52944_853c2_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_853c2_p682f0_w6_r13_pP) C_XA_52944_853c2_p682f0_w6_r13_pP.OBLS [(386%uint63, T_Ubs2UE.T_UW_52944_853c2_w6_r13_pP_L0)] C_XA_52944_853c2_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_853c2_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_853c2_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_853c2_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_fb3a4d5 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_fb3a4d5).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_fb3a4d5) C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.OBLS [(214%uint63, T_Ubs2UE.T_XA_52944_853c2_blk_w7_r14_L0); (215%uint63, T_Ubs2UE.T_XA_52944_853c2_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_fb3a4d5.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_853c2_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_853c2_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.OBLS [(270%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_fb3a4d5)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fb3a4d5.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_fb3a4d5 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_c50a9_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_c50a9_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_c50a9_w7_r14_pv_L0.CTX C_UW_52944_c50a9_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_c50a9_w7_r14_pv_L0) C_UW_52944_c50a9_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_c50a9_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_c50a9_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_c50a9_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_c50a9_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_c50a9_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_c50a9_blk_w7_r14_L0.CTX C_XA_52944_c50a9_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_c50a9_blk_w7_r14_L0) C_XA_52944_c50a9_blk_w7_r14_L0.OBLS [(401%uint63, T_Ubs2UE.T_UW_52944_c50a9_w7_r14_pv_L0)] C_XA_52944_c50a9_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_c50a9_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_c50a9_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_c50a9_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_c50a9_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_c50a9_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_c50a9_w6_r13_pP_L0.CTX C_UW_52944_c50a9_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_c50a9_w6_r13_pP_L0) C_UW_52944_c50a9_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_c50a9_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_c50a9_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_c50a9_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_c50a9_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_c50a9_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_c50a9_p682f0_w6_r13_pP.CTX C_XA_52944_c50a9_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_c50a9_p682f0_w6_r13_pP) C_XA_52944_c50a9_p682f0_w6_r13_pP.OBLS [(400%uint63, T_Ubs2UE.T_UW_52944_c50a9_w6_r13_pP_L0)] C_XA_52944_c50a9_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_c50a9_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_c50a9_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_c50a9_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_14.
