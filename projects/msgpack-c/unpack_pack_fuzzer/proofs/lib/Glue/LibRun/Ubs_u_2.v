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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require B_02.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_02 B_06 B_07.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.
Module C_UW_236d8_175a8_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_175a8_w7_r14_pv_L0.
Module C_UW_236d8_1cfef_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_1cfef_w6_r13_pP_L0.
Module C_UW_236d8_1cfef_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_1cfef_w7_r14_pv_L0.
Module C_UW_236d8_3e1cd_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_3e1cd_w6_r13_pP_L0.
Module C_UW_236d8_3e1cd_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_3e1cd_w7_r14_pv_L0.
Module C_UW_236d8_6a133_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_6a133_w6_r13_pP_L0.
Module C_UW_236d8_6a133_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_6a133_w7_r14_pv_L0.
Module C_UW_236d8_6db84_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_6db84_w6_r13_pP_L0.
Module C_UW_236d8_6db84_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_6db84_w7_r14_pv_L0.
Module C_UW_236d8_8204c_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_8204c_w6_r13_pP_L0.
Module C_UW_236d8_8204c_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_8204c_w7_r14_pv_L0.
Module C_UW_236d8_ea939_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_ea939_w6_r13_pP_L0.
Module C_UW_236d8_ea939_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_ea939_w7_r14_pv_L0.
Module C_XA_236d8_175a8_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_175a8_blk_w7_r14_L0.
Module C_XA_236d8_1cfef_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_1cfef_blk_w7_r14_L0.
Module C_XA_236d8_1cfef_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_1cfef_p682f0_w6_r13_pP.
Module C_XA_236d8_3e1cd_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_3e1cd_blk_w7_r14_L0.
Module C_XA_236d8_3e1cd_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_3e1cd_p682f0_w6_r13_pP.
Module C_XA_236d8_6a133_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_6a133_blk_w7_r14_L0.
Module C_XA_236d8_6a133_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_6a133_p682f0_w6_r13_pP.
Module C_XA_236d8_6db84_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_6db84_blk_w7_r14_L0.
Module C_XA_236d8_6db84_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_6db84_p682f0_w6_r13_pP.
Module C_XA_236d8_8204c_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_8204c_blk_w7_r14_L0.
Module C_XA_236d8_8204c_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_8204c_p682f0_w6_r13_pP.
Module C_XA_236d8_ea939_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_ea939_blk_w7_r14_L0.
Module C_XA_236d8_ea939_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_ea939_p682f0_w6_r13_pP.
Import Ubs_u_1.LibRunUbs_u_1.

Module LibRunUbs_u_2.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6) C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.OBLS [(188%uint63, T_Ubs2UE.T_XA_236d8_c92f2_blk_w7_r14_L0); (189%uint63, T_Ubs2UE.T_XA_236d8_c92f2_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_c92f2_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_c92f2_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.OBLS [(300%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f2dbbe6 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_ea939_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_ea939_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_ea939_w7_r14_pv_L0.CTX C_UW_236d8_ea939_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_ea939_w7_r14_pv_L0) C_UW_236d8_ea939_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_ea939_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_ea939_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_ea939_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_ea939_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_ea939_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_ea939_blk_w7_r14_L0.CTX C_XA_236d8_ea939_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_ea939_blk_w7_r14_L0) C_XA_236d8_ea939_blk_w7_r14_L0.OBLS [(363%uint63, T_Ubs2UE.T_UW_236d8_ea939_w7_r14_pv_L0)] C_XA_236d8_ea939_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_ea939_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_ea939_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_ea939_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_ea939_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_ea939_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_ea939_w6_r13_pP_L0.CTX C_UW_236d8_ea939_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_ea939_w6_r13_pP_L0) C_UW_236d8_ea939_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_ea939_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_ea939_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_ea939_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_ea939_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_ea939_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_ea939_p682f0_w6_r13_pP.CTX C_XA_236d8_ea939_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_ea939_p682f0_w6_r13_pP) C_XA_236d8_ea939_p682f0_w6_r13_pP.OBLS [(362%uint63, T_Ubs2UE.T_UW_236d8_ea939_w6_r13_pP_L0)] C_XA_236d8_ea939_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_ea939_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_ea939_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_ea939_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2) C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.OBLS [(190%uint63, T_Ubs2UE.T_XA_236d8_ea939_blk_w7_r14_L0); (191%uint63, T_Ubs2UE.T_XA_236d8_ea939_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f8199b2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_ea939_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_ea939_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.OBLS [(301%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f8199b2 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_6db84_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_6db84_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_6db84_w7_r14_pv_L0.CTX C_UW_236d8_6db84_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_6db84_w7_r14_pv_L0) C_UW_236d8_6db84_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_6db84_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_6db84_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_6db84_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_6db84_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_6db84_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_6db84_blk_w7_r14_L0.CTX C_XA_236d8_6db84_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_6db84_blk_w7_r14_L0) C_XA_236d8_6db84_blk_w7_r14_L0.OBLS [(351%uint63, T_Ubs2UE.T_UW_236d8_6db84_w7_r14_pv_L0)] C_XA_236d8_6db84_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_6db84_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_6db84_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_6db84_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_6db84_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_6db84_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_6db84_w6_r13_pP_L0.CTX C_UW_236d8_6db84_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_6db84_w6_r13_pP_L0) C_UW_236d8_6db84_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_6db84_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_6db84_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_6db84_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_6db84_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_6db84_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_6db84_p682f0_w6_r13_pP.CTX C_XA_236d8_6db84_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_6db84_p682f0_w6_r13_pP) C_XA_236d8_6db84_p682f0_w6_r13_pP.OBLS [(350%uint63, T_Ubs2UE.T_UW_236d8_6db84_w6_r13_pP_L0)] C_XA_236d8_6db84_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_6db84_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_6db84_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_6db84_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e) C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.OBLS [(178%uint63, T_Ubs2UE.T_XA_236d8_6db84_blk_w7_r14_L0); (179%uint63, T_Ubs2UE.T_XA_236d8_6db84_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_fcd577e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_6db84_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_6db84_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.OBLS [(302%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcd577e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_1cfef_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_1cfef_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_1cfef_w7_r14_pv_L0.CTX C_UW_236d8_1cfef_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_1cfef_w7_r14_pv_L0) C_UW_236d8_1cfef_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_1cfef_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_1cfef_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_1cfef_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_1cfef_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_1cfef_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_1cfef_blk_w7_r14_L0.CTX C_XA_236d8_1cfef_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_1cfef_blk_w7_r14_L0) C_XA_236d8_1cfef_blk_w7_r14_L0.OBLS [(343%uint63, T_Ubs2UE.T_UW_236d8_1cfef_w7_r14_pv_L0)] C_XA_236d8_1cfef_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_1cfef_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_1cfef_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_1cfef_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_1cfef_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_1cfef_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_1cfef_w6_r13_pP_L0.CTX C_UW_236d8_1cfef_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_1cfef_w6_r13_pP_L0) C_UW_236d8_1cfef_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_1cfef_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_1cfef_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_1cfef_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_1cfef_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_1cfef_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_1cfef_p682f0_w6_r13_pP.CTX C_XA_236d8_1cfef_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_1cfef_p682f0_w6_r13_pP) C_XA_236d8_1cfef_p682f0_w6_r13_pP.OBLS [(342%uint63, T_Ubs2UE.T_UW_236d8_1cfef_w6_r13_pP_L0)] C_XA_236d8_1cfef_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_1cfef_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_1cfef_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_1cfef_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6) C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.OBLS [(170%uint63, T_Ubs2UE.T_XA_236d8_1cfef_blk_w7_r14_L0); (171%uint63, T_Ubs2UE.T_XA_236d8_1cfef_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_fd804b6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_1cfef_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_1cfef_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.OBLS [(305%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fd804b6 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_3e1cd_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_3e1cd_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_3e1cd_w7_r14_pv_L0.CTX C_UW_236d8_3e1cd_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_3e1cd_w7_r14_pv_L0) C_UW_236d8_3e1cd_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_3e1cd_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_3e1cd_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_3e1cd_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_3e1cd_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_3e1cd_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_3e1cd_blk_w7_r14_L0.CTX C_XA_236d8_3e1cd_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_3e1cd_blk_w7_r14_L0) C_XA_236d8_3e1cd_blk_w7_r14_L0.OBLS [(345%uint63, T_Ubs2UE.T_UW_236d8_3e1cd_w7_r14_pv_L0)] C_XA_236d8_3e1cd_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_3e1cd_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_3e1cd_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_3e1cd_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_3e1cd_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_3e1cd_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_3e1cd_w6_r13_pP_L0.CTX C_UW_236d8_3e1cd_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_3e1cd_w6_r13_pP_L0) C_UW_236d8_3e1cd_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_3e1cd_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_3e1cd_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_3e1cd_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_3e1cd_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_3e1cd_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_3e1cd_p682f0_w6_r13_pP.CTX C_XA_236d8_3e1cd_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_3e1cd_p682f0_w6_r13_pP) C_XA_236d8_3e1cd_p682f0_w6_r13_pP.OBLS [(344%uint63, T_Ubs2UE.T_UW_236d8_3e1cd_w6_r13_pP_L0)] C_XA_236d8_3e1cd_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_3e1cd_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_3e1cd_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_3e1cd_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d) C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.OBLS [(172%uint63, T_Ubs2UE.T_XA_236d8_3e1cd_blk_w7_r14_L0); (173%uint63, T_Ubs2UE.T_XA_236d8_3e1cd_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f87081d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_3e1cd_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_3e1cd_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.OBLS [(308%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f87081d _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_6a133_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_6a133_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_6a133_w7_r14_pv_L0.CTX C_UW_236d8_6a133_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_6a133_w7_r14_pv_L0) C_UW_236d8_6a133_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_6a133_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_6a133_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_6a133_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_6a133_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_6a133_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_6a133_blk_w7_r14_L0.CTX C_XA_236d8_6a133_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_6a133_blk_w7_r14_L0) C_XA_236d8_6a133_blk_w7_r14_L0.OBLS [(349%uint63, T_Ubs2UE.T_UW_236d8_6a133_w7_r14_pv_L0)] C_XA_236d8_6a133_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_6a133_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_6a133_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_6a133_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_6a133_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_6a133_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_6a133_w6_r13_pP_L0.CTX C_UW_236d8_6a133_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_6a133_w6_r13_pP_L0) C_UW_236d8_6a133_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_6a133_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_6a133_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_6a133_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_6a133_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_6a133_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_6a133_p682f0_w6_r13_pP.CTX C_XA_236d8_6a133_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_6a133_p682f0_w6_r13_pP) C_XA_236d8_6a133_p682f0_w6_r13_pP.OBLS [(348%uint63, T_Ubs2UE.T_UW_236d8_6a133_w6_r13_pP_L0)] C_XA_236d8_6a133_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_6a133_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_6a133_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_6a133_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20) C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.OBLS [(176%uint63, T_Ubs2UE.T_XA_236d8_6a133_blk_w7_r14_L0); (177%uint63, T_Ubs2UE.T_XA_236d8_6a133_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f341c20.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_6a133_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_6a133_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.OBLS [(309%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f341c20 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_8204c_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_8204c_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_8204c_w7_r14_pv_L0.CTX C_UW_236d8_8204c_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_8204c_w7_r14_pv_L0) C_UW_236d8_8204c_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_8204c_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_8204c_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_8204c_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_8204c_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_8204c_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_8204c_blk_w7_r14_L0.CTX C_XA_236d8_8204c_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_8204c_blk_w7_r14_L0) C_XA_236d8_8204c_blk_w7_r14_L0.OBLS [(353%uint63, T_Ubs2UE.T_UW_236d8_8204c_w7_r14_pv_L0)] C_XA_236d8_8204c_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_8204c_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_8204c_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_8204c_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_8204c_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_8204c_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_8204c_w6_r13_pP_L0.CTX C_UW_236d8_8204c_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_8204c_w6_r13_pP_L0) C_UW_236d8_8204c_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_8204c_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_8204c_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_8204c_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_8204c_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_8204c_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_8204c_p682f0_w6_r13_pP.CTX C_XA_236d8_8204c_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_8204c_p682f0_w6_r13_pP) C_XA_236d8_8204c_p682f0_w6_r13_pP.OBLS [(352%uint63, T_Ubs2UE.T_UW_236d8_8204c_w6_r13_pP_L0)] C_XA_236d8_8204c_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_8204c_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_8204c_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_8204c_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637) C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.OBLS [(180%uint63, T_Ubs2UE.T_XA_236d8_8204c_blk_w7_r14_L0); (181%uint63, T_Ubs2UE.T_XA_236d8_8204c_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f853637.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_8204c_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_8204c_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.OBLS [(310%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f853637 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_175a8_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_175a8_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_175a8_w7_r14_pv_L0.CTX C_UW_236d8_175a8_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_175a8_w7_r14_pv_L0) C_UW_236d8_175a8_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_175a8_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_175a8_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_175a8_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_175a8_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_175a8_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_175a8_blk_w7_r14_L0.CTX C_XA_236d8_175a8_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_175a8_blk_w7_r14_L0) C_XA_236d8_175a8_blk_w7_r14_L0.OBLS [(341%uint63, T_Ubs2UE.T_UW_236d8_175a8_w7_r14_pv_L0)] C_XA_236d8_175a8_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_175a8_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_175a8_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_175a8_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_2.
