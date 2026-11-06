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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_03 B_04 B_05 B_09 B_10 B_11 B_16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.
Module C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.
Module C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.
Module C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.
Module C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.
Module C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.
Module C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.
Module C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.
Module C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.
Module C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.
Module C_UW_223c4_63bac_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_63bac_w6_r13_pP_L0.
Module C_UW_223c4_63bac_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_63bac_w7_r14_pv_L0.
Module C_UW_223c4_83af5_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_83af5_w6_r13_pP_L0.
Module C_UW_223c4_83af5_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_83af5_w7_r14_pv_L0.
Module C_UW_223c4_982fd_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_982fd_w6_r13_pP_L0.
Module C_UW_22558_a059b_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22558_a059b_w7_r14_pP_L0.
Module C_UW_22558_a059b_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22558_a059b_w8_r15_pv_L0.
Module C_UW_22558_fe93b_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22558_fe93b_w8_r15_pv_L0.
Module C_UW_52944_3a9b1_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_3a9b1_w6_r13_pP_L0.
Module C_UW_52944_3a9b1_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_3a9b1_w7_r14_pP_L0.
Module C_UW_52944_fce48_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_UW_52944_fce48_w7_r14_pP_L0.
Module C_UW_52944_fce48_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_UW_52944_fce48_w8_r15_pv_L0.
Module C_UW_52944_ff71a_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_UW_52944_ff71a_w7_r14_pP_L0.
Module C_UW_52944_ff71a_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_UW_52944_ff71a_w8_r15_pv_L0.
Module C_XA_223c4_63bac_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_63bac_blk_w7_r14_L0.
Module C_XA_223c4_63bac_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_63bac_p682f0_w6_r13_pP.
Module C_XA_223c4_83af5_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_83af5_blk_w7_r14_L0.
Module C_XA_223c4_83af5_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_83af5_p682f0_w6_r13_pP.
Module C_XA_223c4_982fd_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_982fd_blk_w7_r14_L0.
Module C_XA_223c4_982fd_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_982fd_p682f0_w6_r13_pP.
Module C_XA_22558_a059b_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22558_a059b_blk_w7_r14_L0.
Module C_XA_22558_a059b_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22558_a059b_p682f0_w6_r13_pP.
Module C_XA_22558_fe93b_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22558_fe93b_blk_w7_r14_L0.
Module C_XA_52944_3a9b1_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_3a9b1_blk_w7_r14_L0.
Module C_XA_52944_3a9b1_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_3a9b1_p68250_w6_r13_pP.
Module C_XA_52944_fce48_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_fce48_blk_w8_r15_L0.
Module C_XA_52944_fce48_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_fce48_p682f0_w7_r14_pP.
Module C_XA_52944_ff71a_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_ff71a_blk_w8_r15_L0.
Module C_XA_52944_ff71a_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_ff71a_p682f0_w7_r14_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4.

Module LibRunUbs_u_5.
Lemma LN_TUE_T_XA_223c4_982fd_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_982fd_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_982fd_blk_w7_r14_L0.CTX C_XA_223c4_982fd_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_223c4_982fd_blk_w7_r14_L0) C_XA_223c4_982fd_blk_w7_r14_L0.OBLS [(301%uint63, T_Ubs2UE.T_UW_223c4_982fd_w7_r14_pv_L0)] C_XA_223c4_982fd_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_982fd_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_982fd_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_982fd_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_982fd_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_982fd_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_982fd_w6_r13_pP_L0.CTX C_UW_223c4_982fd_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_982fd_w6_r13_pP_L0) C_UW_223c4_982fd_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_223c4_982fd_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_982fd_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_982fd_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_982fd_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_982fd_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_982fd_p682f0_w6_r13_pP.CTX C_XA_223c4_982fd_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_223c4_982fd_p682f0_w6_r13_pP) C_XA_223c4_982fd_p682f0_w6_r13_pP.OBLS [(300%uint63, T_Ubs2UE.T_UW_223c4_982fd_w6_r13_pP_L0)] C_XA_223c4_982fd_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_982fd_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_982fd_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_982fd_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.CTX C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35) C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.OBLS [(128%uint63, T_Ubs2UE.T_XA_223c4_982fd_blk_w7_r14_L0); (129%uint63, T_Ubs2UE.T_XA_223c4_982fd_p682f0_w6_r13_pP)] C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.WF ITAB_ok (contracts_ok_of SEGS R C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.CTX (@h_ctabUE _ _ _ H)) C_EH_223c4_s8_m5_w6_r13_pv_L0_ff7bc35.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_223c4_982fd_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_223c4_982fd_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.CTX C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.PLAN (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.OBLS [(142%uint63, T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35)] C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_ff7bc35.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_ff7bc35 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_63bac_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_63bac_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_63bac_w7_r14_pv_L0.CTX C_UW_223c4_63bac_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_63bac_w7_r14_pv_L0) C_UW_223c4_63bac_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_223c4_63bac_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_63bac_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_63bac_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_63bac_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_63bac_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_63bac_blk_w7_r14_L0.CTX C_XA_223c4_63bac_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_223c4_63bac_blk_w7_r14_L0) C_XA_223c4_63bac_blk_w7_r14_L0.OBLS [(293%uint63, T_Ubs2UE.T_UW_223c4_63bac_w7_r14_pv_L0)] C_XA_223c4_63bac_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_63bac_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_63bac_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_63bac_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_63bac_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_63bac_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_63bac_w6_r13_pP_L0.CTX C_UW_223c4_63bac_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_63bac_w6_r13_pP_L0) C_UW_223c4_63bac_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_223c4_63bac_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_63bac_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_63bac_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_63bac_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_63bac_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_63bac_p682f0_w6_r13_pP.CTX C_XA_223c4_63bac_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_223c4_63bac_p682f0_w6_r13_pP) C_XA_223c4_63bac_p682f0_w6_r13_pP.OBLS [(292%uint63, T_Ubs2UE.T_UW_223c4_63bac_w6_r13_pP_L0)] C_XA_223c4_63bac_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_63bac_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_63bac_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_63bac_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.CTX C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717) C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.OBLS [(120%uint63, T_Ubs2UE.T_XA_223c4_63bac_blk_w7_r14_L0); (121%uint63, T_Ubs2UE.T_XA_223c4_63bac_p682f0_w6_r13_pP)] C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.WF ITAB_ok (contracts_ok_of SEGS R C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.CTX (@h_ctabUE _ _ _ H)) C_EH_223c4_s8_m5_w6_r13_pv_L0_fc26717.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_223c4_63bac_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_223c4_63bac_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.CTX C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.PLAN (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.OBLS [(143%uint63, T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717)] C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_fc26717.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_fc26717 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_83af5_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_83af5_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_83af5_w7_r14_pv_L0.CTX C_UW_223c4_83af5_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_83af5_w7_r14_pv_L0) C_UW_223c4_83af5_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_223c4_83af5_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_83af5_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_83af5_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_83af5_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_83af5_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_83af5_blk_w7_r14_L0.CTX C_XA_223c4_83af5_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_223c4_83af5_blk_w7_r14_L0) C_XA_223c4_83af5_blk_w7_r14_L0.OBLS [(297%uint63, T_Ubs2UE.T_UW_223c4_83af5_w7_r14_pv_L0)] C_XA_223c4_83af5_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_83af5_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_83af5_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_83af5_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_83af5_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_83af5_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_83af5_w6_r13_pP_L0.CTX C_UW_223c4_83af5_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_83af5_w6_r13_pP_L0) C_UW_223c4_83af5_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_223c4_83af5_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_83af5_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_83af5_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_83af5_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_83af5_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_83af5_p682f0_w6_r13_pP.CTX C_XA_223c4_83af5_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_223c4_83af5_p682f0_w6_r13_pP) C_XA_223c4_83af5_p682f0_w6_r13_pP.OBLS [(296%uint63, T_Ubs2UE.T_UW_223c4_83af5_w6_r13_pP_L0)] C_XA_223c4_83af5_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_83af5_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_83af5_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_83af5_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.CTX C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14) C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.OBLS [(124%uint63, T_Ubs2UE.T_XA_223c4_83af5_blk_w7_r14_L0); (125%uint63, T_Ubs2UE.T_XA_223c4_83af5_p682f0_w6_r13_pP)] C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.WF ITAB_ok (contracts_ok_of SEGS R C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.CTX (@h_ctabUE _ _ _ H)) C_EH_223c4_s8_m5_w6_r13_pv_L0_facbb14.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_223c4_83af5_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_223c4_83af5_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.CTX C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.PLAN (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.OBLS [(144%uint63, T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14)] C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_facbb14.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_facbb14 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_ff71a_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_ff71a_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_ff71a_w8_r15_pv_L0.CTX C_UW_52944_ff71a_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_ff71a_w8_r15_pv_L0) C_UW_52944_ff71a_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_ff71a_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_ff71a_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_ff71a_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_ff71a_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_ff71a_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_ff71a_blk_w8_r15_L0.CTX C_XA_52944_ff71a_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_ff71a_blk_w8_r15_L0) C_XA_52944_ff71a_blk_w8_r15_L0.OBLS [(575%uint63, T_Ubs2UE.T_UW_52944_ff71a_w8_r15_pv_L0)] C_XA_52944_ff71a_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_ff71a_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_ff71a_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_ff71a_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_ff71a_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_ff71a_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_ff71a_w7_r14_pP_L0.CTX C_UW_52944_ff71a_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_ff71a_w7_r14_pP_L0) C_UW_52944_ff71a_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_ff71a_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_ff71a_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_ff71a_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_ff71a_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_ff71a_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_ff71a_p682f0_w7_r14_pP.CTX C_XA_52944_ff71a_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_ff71a_p682f0_w7_r14_pP) C_XA_52944_ff71a_p682f0_w7_r14_pP.OBLS [(574%uint63, T_Ubs2UE.T_UW_52944_ff71a_w7_r14_pP_L0)] C_XA_52944_ff71a_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_ff71a_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_ff71a_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_ff71a_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1) C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.OBLS [(490%uint63, T_Ubs2UE.T_XA_52944_ff71a_blk_w8_r15_L0); (491%uint63, T_Ubs2UE.T_XA_52944_ff71a_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_ff71a_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_ff71a_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22558_a059b_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22558_a059b_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22558_a059b_w8_r15_pv_L0.CTX C_UW_22558_a059b_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22558_a059b_w8_r15_pv_L0) C_UW_22558_a059b_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22558_a059b_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22558_a059b_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22558_a059b_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22558_a059b_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22558_a059b_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22558_a059b_blk_w7_r14_L0.CTX C_XA_22558_a059b_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22558_a059b_blk_w7_r14_L0) C_XA_22558_a059b_blk_w7_r14_L0.OBLS [(242%uint63, T_Ubs2UE.T_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1); (305%uint63, T_Ubs2UE.T_UW_22558_a059b_w8_r15_pv_L0)] C_XA_22558_a059b_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22558_a059b_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22558_a059b_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22558_a059b_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22558_a059b_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_3a9b1_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_3a9b1_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_3a9b1_w7_r14_pP_L0.CTX C_UW_52944_3a9b1_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_3a9b1_w7_r14_pP_L0) C_UW_52944_3a9b1_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_3a9b1_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_3a9b1_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_3a9b1_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_3a9b1_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_3a9b1_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_3a9b1_blk_w7_r14_L0.CTX C_XA_52944_3a9b1_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_3a9b1_blk_w7_r14_L0) C_XA_52944_3a9b1_blk_w7_r14_L0.OBLS [(513%uint63, T_Ubs2UE.T_UW_52944_3a9b1_w7_r14_pP_L0)] C_XA_52944_3a9b1_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_3a9b1_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_3a9b1_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_3a9b1_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_3a9b1_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_3a9b1_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_3a9b1_w6_r13_pP_L0.CTX C_UW_52944_3a9b1_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_3a9b1_w6_r13_pP_L0) C_UW_52944_3a9b1_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_3a9b1_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_3a9b1_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_3a9b1_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_3a9b1_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_3a9b1_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_3a9b1_p68250_w6_r13_pP.CTX C_XA_52944_3a9b1_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_3a9b1_p68250_w6_r13_pP) C_XA_52944_3a9b1_p68250_w6_r13_pP.OBLS [(512%uint63, T_Ubs2UE.T_UW_52944_3a9b1_w6_r13_pP_L0)] C_XA_52944_3a9b1_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_3a9b1_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_3a9b1_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_3a9b1_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.OBLS [(428%uint63, T_Ubs2UE.T_XA_52944_3a9b1_blk_w7_r14_L0); (429%uint63, T_Ubs2UE.T_XA_52944_3a9b1_p68250_w6_r13_pP)] C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_3a9b1_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_3a9b1_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22558_a059b_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22558_a059b_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22558_a059b_w7_r14_pP_L0.CTX C_UW_22558_a059b_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22558_a059b_w7_r14_pP_L0) C_UW_22558_a059b_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22558_a059b_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22558_a059b_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22558_a059b_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22558_a059b_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22558_a059b_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22558_a059b_p682f0_w6_r13_pP.CTX C_XA_22558_a059b_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22558_a059b_p682f0_w6_r13_pP) C_XA_22558_a059b_p682f0_w6_r13_pP.OBLS [(243%uint63, T_Ubs2UE.T_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1); (304%uint63, T_Ubs2UE.T_UW_22558_a059b_w7_r14_pP_L0)] C_XA_22558_a059b_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22558_a059b_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22558_a059b_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22558_a059b_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22558_a059b_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.CTX C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.PLAN (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca) C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.OBLS [(132%uint63, T_Ubs2UE.T_XA_22558_a059b_blk_w7_r14_L0); (133%uint63, T_Ubs2UE.T_XA_22558_a059b_p682f0_w6_r13_pP)] C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.CTX (@h_ctabUE _ _ _ H)) C_EH_22558_s10_m5_w6_r13_pv_L0_f5d1dca.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22558_a059b_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22558_a059b_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.CTX C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.PLAN (t_st T_Ubs2U.T_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca) C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.OBLS [(145%uint63, T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca)] C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_f5d1dca.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22558_s10_m5_w6_r13_pv_L0_f5d1dca _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_fce48_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_fce48_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_fce48_w8_r15_pv_L0.CTX C_UW_52944_fce48_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_fce48_w8_r15_pv_L0) C_UW_52944_fce48_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_fce48_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_fce48_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_fce48_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_fce48_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_fce48_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_fce48_blk_w8_r15_L0.CTX C_XA_52944_fce48_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_fce48_blk_w8_r15_L0) C_XA_52944_fce48_blk_w8_r15_L0.OBLS [(573%uint63, T_Ubs2UE.T_UW_52944_fce48_w8_r15_pv_L0)] C_XA_52944_fce48_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_fce48_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_fce48_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_fce48_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_fce48_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_fce48_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_fce48_w7_r14_pP_L0.CTX C_UW_52944_fce48_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_fce48_w7_r14_pP_L0) C_UW_52944_fce48_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_fce48_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_fce48_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_fce48_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_fce48_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_fce48_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_fce48_p682f0_w7_r14_pP.CTX C_XA_52944_fce48_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_fce48_p682f0_w7_r14_pP) C_XA_52944_fce48_p682f0_w7_r14_pP.OBLS [(572%uint63, T_Ubs2UE.T_UW_52944_fce48_w7_r14_pP_L0)] C_XA_52944_fce48_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_fce48_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_fce48_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_fce48_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1) C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.OBLS [(488%uint63, T_Ubs2UE.T_XA_52944_fce48_blk_w8_r15_L0); (489%uint63, T_Ubs2UE.T_XA_52944_fce48_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_fce48_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_fce48_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22558_fe93b_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22558_fe93b_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22558_fe93b_w8_r15_pv_L0.CTX C_UW_22558_fe93b_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22558_fe93b_w8_r15_pv_L0) C_UW_22558_fe93b_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22558_fe93b_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22558_fe93b_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22558_fe93b_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22558_fe93b_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22558_fe93b_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22558_fe93b_blk_w7_r14_L0.CTX C_XA_22558_fe93b_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22558_fe93b_blk_w7_r14_L0) C_XA_22558_fe93b_blk_w7_r14_L0.OBLS [(244%uint63, T_Ubs2UE.T_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1); (307%uint63, T_Ubs2UE.T_UW_22558_fe93b_w8_r15_pv_L0)] C_XA_22558_fe93b_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22558_fe93b_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22558_fe93b_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22558_fe93b_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22558_fe93b_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_5.
