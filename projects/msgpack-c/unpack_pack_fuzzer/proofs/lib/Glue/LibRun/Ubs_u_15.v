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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_02 B_03 B_07 B_08.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5 Ubs_u_6 Ubs_u_7 Ubs_u_8 Ubs_u_9 Ubs_u_10 Ubs_u_11 Ubs_u_12 Ubs_u_13 Ubs_u_14.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.
Module C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.
Module C_UW_52944_079b6_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_079b6_w6_r13_pP_L0.
Module C_UW_52944_079b6_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_079b6_w7_r14_pv_L0.
Module C_UW_52944_0db6b_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_0db6b_w6_r13_pP_L0.
Module C_UW_52944_0db6b_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_0db6b_w7_r14_pv_L0.
Module C_UW_52944_2a6cb_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_2a6cb_w6_r13_pP_L0.
Module C_UW_52944_2a6cb_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_2a6cb_w7_r14_pv_L0.
Module C_UW_52944_63732_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_63732_w6_r13_pP_L0.
Module C_UW_52944_63732_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_63732_w7_r14_pv_L0.
Module C_UW_52944_8bc0a_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_8bc0a_w6_r13_pP_L0.
Module C_UW_52944_8bc0a_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_8bc0a_w7_r14_pv_L0.
Module C_UW_52944_af6c4_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_af6c4_w6_r13_pP_L0.
Module C_UW_52944_af6c4_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_af6c4_w7_r14_pv_L0.
Module C_UW_52944_bd003_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_bd003_w7_r14_pv_L0.
Module C_XA_52944_079b6_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_079b6_blk_w7_r14_L0.
Module C_XA_52944_079b6_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_079b6_p682f0_w6_r13_pP.
Module C_XA_52944_0db6b_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_0db6b_blk_w7_r14_L0.
Module C_XA_52944_0db6b_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_0db6b_p682f0_w6_r13_pP.
Module C_XA_52944_2a6cb_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_2a6cb_blk_w7_r14_L0.
Module C_XA_52944_2a6cb_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_2a6cb_p682f0_w6_r13_pP.
Module C_XA_52944_63732_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_63732_blk_w7_r14_L0.
Module C_XA_52944_63732_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_63732_p682f0_w6_r13_pP.
Module C_XA_52944_8bc0a_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_8bc0a_blk_w7_r14_L0.
Module C_XA_52944_8bc0a_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_8bc0a_p682f0_w6_r13_pP.
Module C_XA_52944_af6c4_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_af6c4_blk_w7_r14_L0.
Module C_XA_52944_af6c4_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_af6c4_p682f0_w6_r13_pP.
Module C_XA_52944_bd003_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_XA_52944_bd003_blk_w7_r14_L0.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4 Ubs_u_5.LibRunUbs_u_5 Ubs_u_6.LibRunUbs_u_6 Ubs_u_7.LibRunUbs_u_7 Ubs_u_8.LibRunUbs_u_8 Ubs_u_9.LibRunUbs_u_9 Ubs_u_10.LibRunUbs_u_10 Ubs_u_11.LibRunUbs_u_11 Ubs_u_12.LibRunUbs_u_12 Ubs_u_13.LibRunUbs_u_13 Ubs_u_14.LibRunUbs_u_14.

Module LibRunUbs_u_15.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb) C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.OBLS [(228%uint63, T_Ubs2UE.T_XA_52944_c50a9_blk_w7_r14_L0); (229%uint63, T_Ubs2UE.T_XA_52944_c50a9_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f37e2fb.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_c50a9_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_c50a9_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.OBLS [(271%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f37e2fb.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f37e2fb _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_63732_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_63732_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_63732_w7_r14_pv_L0.CTX C_UW_52944_63732_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_63732_w7_r14_pv_L0) C_UW_52944_63732_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_63732_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_63732_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_63732_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_63732_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_63732_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_63732_blk_w7_r14_L0.CTX C_XA_52944_63732_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_63732_blk_w7_r14_L0) C_XA_52944_63732_blk_w7_r14_L0.OBLS [(381%uint63, T_Ubs2UE.T_UW_52944_63732_w7_r14_pv_L0)] C_XA_52944_63732_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_63732_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_63732_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_63732_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_63732_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_63732_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_63732_w6_r13_pP_L0.CTX C_UW_52944_63732_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_63732_w6_r13_pP_L0) C_UW_52944_63732_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_63732_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_63732_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_63732_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_63732_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_63732_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_63732_p682f0_w6_r13_pP.CTX C_XA_52944_63732_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_63732_p682f0_w6_r13_pP) C_XA_52944_63732_p682f0_w6_r13_pP.OBLS [(380%uint63, T_Ubs2UE.T_UW_52944_63732_w6_r13_pP_L0)] C_XA_52944_63732_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_63732_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_63732_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_63732_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d) C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.OBLS [(208%uint63, T_Ubs2UE.T_XA_52944_63732_blk_w7_r14_L0); (209%uint63, T_Ubs2UE.T_XA_52944_63732_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f47233d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_63732_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_63732_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.OBLS [(272%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f47233d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f47233d _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_af6c4_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_af6c4_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_af6c4_w7_r14_pv_L0.CTX C_UW_52944_af6c4_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_af6c4_w7_r14_pv_L0) C_UW_52944_af6c4_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_af6c4_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_af6c4_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_af6c4_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_af6c4_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_af6c4_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_af6c4_blk_w7_r14_L0.CTX C_XA_52944_af6c4_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_af6c4_blk_w7_r14_L0) C_XA_52944_af6c4_blk_w7_r14_L0.OBLS [(391%uint63, T_Ubs2UE.T_UW_52944_af6c4_w7_r14_pv_L0)] C_XA_52944_af6c4_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_af6c4_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_af6c4_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_af6c4_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_af6c4_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_af6c4_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_af6c4_w6_r13_pP_L0.CTX C_UW_52944_af6c4_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_af6c4_w6_r13_pP_L0) C_UW_52944_af6c4_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_af6c4_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_af6c4_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_af6c4_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_af6c4_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_af6c4_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_af6c4_p682f0_w6_r13_pP.CTX C_XA_52944_af6c4_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_af6c4_p682f0_w6_r13_pP) C_XA_52944_af6c4_p682f0_w6_r13_pP.OBLS [(390%uint63, T_Ubs2UE.T_UW_52944_af6c4_w6_r13_pP_L0)] C_XA_52944_af6c4_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_af6c4_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_af6c4_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_af6c4_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f) C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.OBLS [(218%uint63, T_Ubs2UE.T_XA_52944_af6c4_blk_w7_r14_L0); (219%uint63, T_Ubs2UE.T_XA_52944_af6c4_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f29322f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_af6c4_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_af6c4_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.OBLS [(274%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f29322f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f29322f _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_0db6b_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_0db6b_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_0db6b_w7_r14_pv_L0.CTX C_UW_52944_0db6b_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_0db6b_w7_r14_pv_L0) C_UW_52944_0db6b_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_0db6b_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_0db6b_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_0db6b_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_0db6b_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_0db6b_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_0db6b_blk_w7_r14_L0.CTX C_XA_52944_0db6b_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_0db6b_blk_w7_r14_L0) C_XA_52944_0db6b_blk_w7_r14_L0.OBLS [(369%uint63, T_Ubs2UE.T_UW_52944_0db6b_w7_r14_pv_L0)] C_XA_52944_0db6b_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_0db6b_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_0db6b_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_0db6b_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_0db6b_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_0db6b_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_0db6b_w6_r13_pP_L0.CTX C_UW_52944_0db6b_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_0db6b_w6_r13_pP_L0) C_UW_52944_0db6b_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_0db6b_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_0db6b_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_0db6b_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_0db6b_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_0db6b_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_0db6b_p682f0_w6_r13_pP.CTX C_XA_52944_0db6b_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_0db6b_p682f0_w6_r13_pP) C_XA_52944_0db6b_p682f0_w6_r13_pP.OBLS [(368%uint63, T_Ubs2UE.T_UW_52944_0db6b_w6_r13_pP_L0)] C_XA_52944_0db6b_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_0db6b_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_0db6b_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_0db6b_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e) C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.OBLS [(196%uint63, T_Ubs2UE.T_XA_52944_0db6b_blk_w7_r14_L0); (197%uint63, T_Ubs2UE.T_XA_52944_0db6b_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f0edd6e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_0db6b_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_0db6b_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.OBLS [(275%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f0edd6e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f0edd6e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_079b6_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_079b6_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_079b6_w7_r14_pv_L0.CTX C_UW_52944_079b6_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_079b6_w7_r14_pv_L0) C_UW_52944_079b6_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_079b6_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_079b6_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_079b6_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_079b6_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_079b6_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_079b6_blk_w7_r14_L0.CTX C_XA_52944_079b6_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_079b6_blk_w7_r14_L0) C_XA_52944_079b6_blk_w7_r14_L0.OBLS [(367%uint63, T_Ubs2UE.T_UW_52944_079b6_w7_r14_pv_L0)] C_XA_52944_079b6_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_079b6_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_079b6_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_079b6_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_079b6_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_079b6_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_079b6_w6_r13_pP_L0.CTX C_UW_52944_079b6_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_079b6_w6_r13_pP_L0) C_UW_52944_079b6_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_079b6_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_079b6_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_079b6_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_079b6_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_079b6_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_079b6_p682f0_w6_r13_pP.CTX C_XA_52944_079b6_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_079b6_p682f0_w6_r13_pP) C_XA_52944_079b6_p682f0_w6_r13_pP.OBLS [(366%uint63, T_Ubs2UE.T_UW_52944_079b6_w6_r13_pP_L0)] C_XA_52944_079b6_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_079b6_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_079b6_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_079b6_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_fbda383 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_fbda383).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_fbda383) C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.OBLS [(194%uint63, T_Ubs2UE.T_XA_52944_079b6_blk_w7_r14_L0); (195%uint63, T_Ubs2UE.T_XA_52944_079b6_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_fbda383.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_079b6_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_079b6_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.OBLS [(276%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_fbda383)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_fbda383.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_fbda383 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_8bc0a_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_8bc0a_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_8bc0a_w7_r14_pv_L0.CTX C_UW_52944_8bc0a_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_8bc0a_w7_r14_pv_L0) C_UW_52944_8bc0a_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_8bc0a_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_8bc0a_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_8bc0a_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_8bc0a_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_8bc0a_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_8bc0a_blk_w7_r14_L0.CTX C_XA_52944_8bc0a_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_8bc0a_blk_w7_r14_L0) C_XA_52944_8bc0a_blk_w7_r14_L0.OBLS [(389%uint63, T_Ubs2UE.T_UW_52944_8bc0a_w7_r14_pv_L0)] C_XA_52944_8bc0a_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_8bc0a_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_8bc0a_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_8bc0a_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_8bc0a_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_8bc0a_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_8bc0a_w6_r13_pP_L0.CTX C_UW_52944_8bc0a_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_8bc0a_w6_r13_pP_L0) C_UW_52944_8bc0a_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_8bc0a_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_8bc0a_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_8bc0a_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_8bc0a_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_8bc0a_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_8bc0a_p682f0_w6_r13_pP.CTX C_XA_52944_8bc0a_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_8bc0a_p682f0_w6_r13_pP) C_XA_52944_8bc0a_p682f0_w6_r13_pP.OBLS [(388%uint63, T_Ubs2UE.T_UW_52944_8bc0a_w6_r13_pP_L0)] C_XA_52944_8bc0a_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_8bc0a_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_8bc0a_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_8bc0a_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d) C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.OBLS [(216%uint63, T_Ubs2UE.T_XA_52944_8bc0a_blk_w7_r14_L0); (217%uint63, T_Ubs2UE.T_XA_52944_8bc0a_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f03df9d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_8bc0a_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_8bc0a_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.OBLS [(277%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f03df9d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f03df9d _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_2a6cb_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_2a6cb_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_2a6cb_w7_r14_pv_L0.CTX C_UW_52944_2a6cb_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_2a6cb_w7_r14_pv_L0) C_UW_52944_2a6cb_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_2a6cb_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_2a6cb_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_2a6cb_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_2a6cb_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_2a6cb_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_2a6cb_blk_w7_r14_L0.CTX C_XA_52944_2a6cb_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_2a6cb_blk_w7_r14_L0) C_XA_52944_2a6cb_blk_w7_r14_L0.OBLS [(373%uint63, T_Ubs2UE.T_UW_52944_2a6cb_w7_r14_pv_L0)] C_XA_52944_2a6cb_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_2a6cb_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_2a6cb_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_2a6cb_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_2a6cb_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_2a6cb_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_2a6cb_w6_r13_pP_L0.CTX C_UW_52944_2a6cb_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_2a6cb_w6_r13_pP_L0) C_UW_52944_2a6cb_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_2a6cb_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_2a6cb_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_2a6cb_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_2a6cb_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_2a6cb_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_2a6cb_p682f0_w6_r13_pP.CTX C_XA_52944_2a6cb_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_2a6cb_p682f0_w6_r13_pP) C_XA_52944_2a6cb_p682f0_w6_r13_pP.OBLS [(372%uint63, T_Ubs2UE.T_UW_52944_2a6cb_w6_r13_pP_L0)] C_XA_52944_2a6cb_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_2a6cb_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_2a6cb_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_2a6cb_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2) C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.OBLS [(200%uint63, T_Ubs2UE.T_XA_52944_2a6cb_blk_w7_r14_L0); (201%uint63, T_Ubs2UE.T_XA_52944_2a6cb_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f133da2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_2a6cb_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_2a6cb_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.CTX C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.PLAN (t_st T_Ubs2U.T_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.OBLS [(279%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2)] C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_52944_s8_m1_w8_r15_pv_L0_f133da2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f133da2 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_bd003_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_bd003_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_bd003_w7_r14_pv_L0.CTX C_UW_52944_bd003_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_bd003_w7_r14_pv_L0) C_UW_52944_bd003_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_bd003_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_bd003_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_bd003_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_bd003_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_bd003_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_bd003_blk_w7_r14_L0.CTX C_XA_52944_bd003_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_bd003_blk_w7_r14_L0) C_XA_52944_bd003_blk_w7_r14_L0.OBLS [(397%uint63, T_Ubs2UE.T_UW_52944_bd003_w7_r14_pv_L0)] C_XA_52944_bd003_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_bd003_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_bd003_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_bd003_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_15.
