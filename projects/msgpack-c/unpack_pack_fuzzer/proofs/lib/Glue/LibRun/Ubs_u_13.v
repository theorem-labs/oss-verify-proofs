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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_02 B_03 B_05 B_06 B_08 B_09 B_10 B_13 B_15.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5 Ubs_u_6 Ubs_u_7 Ubs_u_8 Ubs_u_9 Ubs_u_10 Ubs_u_11 Ubs_u_12.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.
Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.
Module C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f844317 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.
Module C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.
Module C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.
Module C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.
Module C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.
Module C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.
Module C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.
Module C_UW_22a78_ab96b_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a78_ab96b_w7_r14_pP_L0.
Module C_UW_22a78_ab96b_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a78_ab96b_w8_r15_pv_L0.
Module C_UW_22a78_e82d1_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_22a78_e82d1_w7_r14_pP_L0.
Module C_UW_22a78_e82d1_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_22a78_e82d1_w8_r15_pv_L0.
Module C_UW_52944_10d60_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_10d60_w6_r13_pP_L0.
Module C_UW_52944_10d60_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_10d60_w7_r14_pP_L0.
Module C_UW_52944_5942e_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_5942e_w6_r13_pP_L0.
Module C_UW_52944_5942e_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_5942e_w7_r14_pv_L0.
Module C_UW_52944_76b3f_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_76b3f_w7_r14_pP_L0.
Module C_UW_52944_76b3f_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_76b3f_w8_r15_pv_L0.
Module C_UW_52944_86509_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_86509_w6_r13_pP_L0.
Module C_UW_52944_86509_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_86509_w7_r14_pP_L0.
Module C_UW_52944_f50a6_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_f50a6_w7_r14_pP_L0.
Module C_UW_52944_f50a6_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_f50a6_w8_r15_pv_L0.
Module C_XA_22a78_ab96b_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22a78_ab96b_blk_w7_r14_L0.
Module C_XA_22a78_ab96b_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_22a78_ab96b_p682f0_w6_r13_pP.
Module C_XA_22a78_e82d1_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_22a78_e82d1_blk_w7_r14_L0.
Module C_XA_22a78_e82d1_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_22a78_e82d1_p682f0_w6_r13_pP.
Module C_XA_52944_10d60_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_10d60_blk_w7_r14_L0.
Module C_XA_52944_10d60_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_10d60_p68250_w6_r13_pP.
Module C_XA_52944_5942e_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_5942e_blk_w7_r14_L0.
Module C_XA_52944_5942e_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_5942e_p682f0_w6_r13_pP.
Module C_XA_52944_76b3f_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_76b3f_blk_w8_r15_L0.
Module C_XA_52944_76b3f_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_76b3f_p682f0_w7_r14_pP.
Module C_XA_52944_86509_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_86509_blk_w7_r14_L0.
Module C_XA_52944_86509_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_86509_p68250_w6_r13_pP.
Module C_XA_52944_f50a6_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_f50a6_blk_w8_r15_L0.
Module C_XA_52944_f50a6_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_f50a6_p682f0_w7_r14_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4 Ubs_u_5.LibRunUbs_u_5 Ubs_u_6.LibRunUbs_u_6 Ubs_u_7.LibRunUbs_u_7 Ubs_u_8.LibRunUbs_u_8 Ubs_u_9.LibRunUbs_u_9 Ubs_u_10.LibRunUbs_u_10 Ubs_u_11.LibRunUbs_u_11 Ubs_u_12.LibRunUbs_u_12.

Module LibRunUbs_u_13.
Lemma LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.CTX C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2) C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.OBLS [(162%uint63, T_Ubs2UE.T_XA_22a78_fd155_blk_w7_r14_L0); (163%uint63, T_Ubs2UE.T_XA_22a78_fd155_p682f0_w6_r13_pP)] C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.CTX (@h_ctabUE _ _ _ H)) C_EH_22a78_s10_m5_w6_r13_pv_L0_f7455d2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22a78_fd155_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22a78_fd155_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.CTX C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.PLAN (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.OBLS [(226%uint63, T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2)] C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f7455d2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_f7455d2 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_76b3f_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_76b3f_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_76b3f_w8_r15_pv_L0.CTX C_UW_52944_76b3f_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_76b3f_w8_r15_pv_L0) C_UW_52944_76b3f_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_76b3f_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_76b3f_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_76b3f_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_76b3f_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_76b3f_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_76b3f_blk_w8_r15_L0.CTX C_XA_52944_76b3f_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_76b3f_blk_w8_r15_L0) C_XA_52944_76b3f_blk_w8_r15_L0.OBLS [(529%uint63, T_Ubs2UE.T_UW_52944_76b3f_w8_r15_pv_L0)] C_XA_52944_76b3f_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_76b3f_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_76b3f_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_76b3f_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_76b3f_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_76b3f_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_76b3f_w7_r14_pP_L0.CTX C_UW_52944_76b3f_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_76b3f_w7_r14_pP_L0) C_UW_52944_76b3f_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_76b3f_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_76b3f_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_76b3f_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_76b3f_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_76b3f_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_76b3f_p682f0_w7_r14_pP.CTX C_XA_52944_76b3f_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_76b3f_p682f0_w7_r14_pP) C_XA_52944_76b3f_p682f0_w7_r14_pP.OBLS [(528%uint63, T_Ubs2UE.T_UW_52944_76b3f_w7_r14_pP_L0)] C_XA_52944_76b3f_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_76b3f_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_76b3f_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_76b3f_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1) C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.OBLS [(444%uint63, T_Ubs2UE.T_XA_52944_76b3f_blk_w8_r15_L0); (445%uint63, T_Ubs2UE.T_XA_52944_76b3f_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_76b3f_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_76b3f_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_ab96b_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_ab96b_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_ab96b_w8_r15_pv_L0.CTX C_UW_22a78_ab96b_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_ab96b_w8_r15_pv_L0) C_UW_22a78_ab96b_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22a78_ab96b_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_ab96b_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_ab96b_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a78_ab96b_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a78_ab96b_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a78_ab96b_blk_w7_r14_L0.CTX C_XA_22a78_ab96b_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22a78_ab96b_blk_w7_r14_L0) C_XA_22a78_ab96b_blk_w7_r14_L0.OBLS [(266%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1); (329%uint63, T_Ubs2UE.T_UW_22a78_ab96b_w8_r15_pv_L0)] C_XA_22a78_ab96b_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a78_ab96b_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22a78_ab96b_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a78_ab96b_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a78_ab96b_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_86509_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_86509_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_86509_w7_r14_pP_L0.CTX C_UW_52944_86509_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_86509_w7_r14_pP_L0) C_UW_52944_86509_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_86509_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_86509_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_86509_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_86509_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_86509_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_86509_blk_w7_r14_L0.CTX C_XA_52944_86509_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_86509_blk_w7_r14_L0) C_XA_52944_86509_blk_w7_r14_L0.OBLS [(535%uint63, T_Ubs2UE.T_UW_52944_86509_w7_r14_pP_L0)] C_XA_52944_86509_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_86509_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_86509_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_86509_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_86509_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_86509_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_86509_w6_r13_pP_L0.CTX C_UW_52944_86509_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_86509_w6_r13_pP_L0) C_UW_52944_86509_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_86509_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_86509_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_86509_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_86509_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_86509_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_86509_p68250_w6_r13_pP.CTX C_XA_52944_86509_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_86509_p68250_w6_r13_pP) C_XA_52944_86509_p68250_w6_r13_pP.OBLS [(534%uint63, T_Ubs2UE.T_UW_52944_86509_w6_r13_pP_L0)] C_XA_52944_86509_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_86509_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_86509_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_86509_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.OBLS [(450%uint63, T_Ubs2UE.T_XA_52944_86509_blk_w7_r14_L0); (451%uint63, T_Ubs2UE.T_XA_52944_86509_p68250_w6_r13_pP)] C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_86509_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_86509_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_ab96b_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_ab96b_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_ab96b_w7_r14_pP_L0.CTX C_UW_22a78_ab96b_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_ab96b_w7_r14_pP_L0) C_UW_22a78_ab96b_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22a78_ab96b_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_ab96b_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_ab96b_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a78_ab96b_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a78_ab96b_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a78_ab96b_p682f0_w6_r13_pP.CTX C_XA_22a78_ab96b_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22a78_ab96b_p682f0_w6_r13_pP) C_XA_22a78_ab96b_p682f0_w6_r13_pP.OBLS [(267%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1); (328%uint63, T_Ubs2UE.T_UW_22a78_ab96b_w7_r14_pP_L0)] C_XA_22a78_ab96b_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a78_ab96b_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22a78_ab96b_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a78_ab96b_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a78_ab96b_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.CTX C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b) C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.OBLS [(156%uint63, T_Ubs2UE.T_XA_22a78_ab96b_blk_w7_r14_L0); (157%uint63, T_Ubs2UE.T_XA_22a78_ab96b_p682f0_w6_r13_pP)] C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.CTX (@h_ctabUE _ _ _ H)) C_EH_22a78_s10_m5_w6_r13_pv_L0_f563d8b.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22a78_ab96b_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22a78_ab96b_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.CTX C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.PLAN (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.OBLS [(227%uint63, T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b)] C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f563d8b.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_f563d8b _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_f50a6_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_f50a6_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_f50a6_w8_r15_pv_L0.CTX C_UW_52944_f50a6_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_f50a6_w8_r15_pv_L0) C_UW_52944_f50a6_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_f50a6_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_f50a6_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_f50a6_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_f50a6_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_f50a6_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_f50a6_blk_w8_r15_L0.CTX C_XA_52944_f50a6_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_f50a6_blk_w8_r15_L0) C_XA_52944_f50a6_blk_w8_r15_L0.OBLS [(569%uint63, T_Ubs2UE.T_UW_52944_f50a6_w8_r15_pv_L0)] C_XA_52944_f50a6_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_f50a6_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_f50a6_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_f50a6_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_f50a6_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_f50a6_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_f50a6_w7_r14_pP_L0.CTX C_UW_52944_f50a6_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_f50a6_w7_r14_pP_L0) C_UW_52944_f50a6_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_f50a6_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_f50a6_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_f50a6_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_f50a6_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_f50a6_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_f50a6_p682f0_w7_r14_pP.CTX C_XA_52944_f50a6_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_f50a6_p682f0_w7_r14_pP) C_XA_52944_f50a6_p682f0_w7_r14_pP.OBLS [(568%uint63, T_Ubs2UE.T_UW_52944_f50a6_w7_r14_pP_L0)] C_XA_52944_f50a6_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_f50a6_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_f50a6_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_f50a6_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1) C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.OBLS [(484%uint63, T_Ubs2UE.T_XA_52944_f50a6_blk_w8_r15_L0); (485%uint63, T_Ubs2UE.T_XA_52944_f50a6_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_f50a6_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_f50a6_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_e82d1_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_e82d1_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_e82d1_w8_r15_pv_L0.CTX C_UW_22a78_e82d1_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_e82d1_w8_r15_pv_L0) C_UW_22a78_e82d1_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22a78_e82d1_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_e82d1_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_e82d1_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a78_e82d1_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a78_e82d1_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a78_e82d1_blk_w7_r14_L0.CTX C_XA_22a78_e82d1_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22a78_e82d1_blk_w7_r14_L0) C_XA_22a78_e82d1_blk_w7_r14_L0.OBLS [(270%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1); (333%uint63, T_Ubs2UE.T_UW_22a78_e82d1_w8_r15_pv_L0)] C_XA_22a78_e82d1_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a78_e82d1_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22a78_e82d1_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a78_e82d1_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a78_e82d1_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_10d60_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_10d60_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_10d60_w7_r14_pP_L0.CTX C_UW_52944_10d60_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_10d60_w7_r14_pP_L0) C_UW_52944_10d60_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_10d60_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_10d60_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_10d60_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_10d60_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_10d60_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_10d60_blk_w7_r14_L0.CTX C_XA_52944_10d60_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_10d60_blk_w7_r14_L0) C_XA_52944_10d60_blk_w7_r14_L0.OBLS [(493%uint63, T_Ubs2UE.T_UW_52944_10d60_w7_r14_pP_L0)] C_XA_52944_10d60_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_10d60_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_10d60_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_10d60_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_10d60_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_10d60_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_10d60_w6_r13_pP_L0.CTX C_UW_52944_10d60_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_10d60_w6_r13_pP_L0) C_UW_52944_10d60_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_10d60_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_10d60_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_10d60_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_10d60_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_10d60_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_10d60_p68250_w6_r13_pP.CTX C_XA_52944_10d60_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_10d60_p68250_w6_r13_pP) C_XA_52944_10d60_p68250_w6_r13_pP.OBLS [(492%uint63, T_Ubs2UE.T_UW_52944_10d60_w6_r13_pP_L0)] C_XA_52944_10d60_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_10d60_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_10d60_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_10d60_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.OBLS [(408%uint63, T_Ubs2UE.T_XA_52944_10d60_blk_w7_r14_L0); (409%uint63, T_Ubs2UE.T_XA_52944_10d60_p68250_w6_r13_pP)] C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_10d60_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_10d60_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_e82d1_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_e82d1_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_e82d1_w7_r14_pP_L0.CTX C_UW_22a78_e82d1_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_e82d1_w7_r14_pP_L0) C_UW_22a78_e82d1_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22a78_e82d1_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_e82d1_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_e82d1_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a78_e82d1_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a78_e82d1_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a78_e82d1_p682f0_w6_r13_pP.CTX C_XA_22a78_e82d1_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22a78_e82d1_p682f0_w6_r13_pP) C_XA_22a78_e82d1_p682f0_w6_r13_pP.OBLS [(271%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1); (332%uint63, T_Ubs2UE.T_UW_22a78_e82d1_w7_r14_pP_L0)] C_XA_22a78_e82d1_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a78_e82d1_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22a78_e82d1_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a78_e82d1_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a78_e82d1_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.CTX C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0) C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.OBLS [(160%uint63, T_Ubs2UE.T_XA_22a78_e82d1_blk_w7_r14_L0); (161%uint63, T_Ubs2UE.T_XA_22a78_e82d1_p682f0_w6_r13_pP)] C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.CTX (@h_ctabUE _ _ _ H)) C_EH_22a78_s10_m5_w6_r13_pv_L0_fec03a0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22a78_e82d1_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22a78_e82d1_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.CTX C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.PLAN (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.OBLS [(228%uint63, T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0)] C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_fec03a0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_fec03a0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_5942e_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_5942e_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_5942e_w7_r14_pv_L0.CTX C_UW_52944_5942e_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_5942e_w7_r14_pv_L0) C_UW_52944_5942e_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_5942e_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_5942e_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_5942e_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_5942e_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_5942e_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_5942e_blk_w7_r14_L0.CTX C_XA_52944_5942e_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_5942e_blk_w7_r14_L0) C_XA_52944_5942e_blk_w7_r14_L0.OBLS [(379%uint63, T_Ubs2UE.T_UW_52944_5942e_w7_r14_pv_L0)] C_XA_52944_5942e_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_5942e_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_5942e_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_5942e_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_5942e_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_5942e_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_5942e_w6_r13_pP_L0.CTX C_UW_52944_5942e_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_5942e_w6_r13_pP_L0) C_UW_52944_5942e_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_5942e_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_5942e_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_5942e_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_5942e_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_5942e_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_5942e_p682f0_w6_r13_pP.CTX C_XA_52944_5942e_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_5942e_p682f0_w6_r13_pP) C_XA_52944_5942e_p682f0_w6_r13_pP.OBLS [(378%uint63, T_Ubs2UE.T_UW_52944_5942e_w6_r13_pP_L0)] C_XA_52944_5942e_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_5942e_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_5942e_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_5942e_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317) C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.OBLS [(206%uint63, T_Ubs2UE.T_XA_52944_5942e_blk_w7_r14_L0); (207%uint63, T_Ubs2UE.T_XA_52944_5942e_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f844317.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_5942e_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_5942e_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.CTX C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.OBLS [(273%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317)] C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w7_r14_pv_L0_f844317.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f844317 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_13.
