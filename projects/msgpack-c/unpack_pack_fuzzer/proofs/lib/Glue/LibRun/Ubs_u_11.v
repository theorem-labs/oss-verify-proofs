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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_02 B_03 B_05 B_06 B_09 B_10 B_11 B_13 B_14.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5 Ubs_u_6 Ubs_u_7 Ubs_u_8 Ubs_u_9 Ubs_u_10.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.
Module C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.
Module C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.
Module C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.
Module C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.
Module C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.
Module C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.
Module C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.
Module C_UW_22594_7b220_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_7b220_w7_r14_pP_L0.
Module C_UW_22594_7b220_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_7b220_w8_r15_pv_L0.
Module C_UW_22a78_515a8_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a78_515a8_w8_r15_pv_L0.
Module C_UW_22a78_d91f1_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_22a78_d91f1_w7_r14_pP_L0.
Module C_UW_22a78_d91f1_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_22a78_d91f1_w8_r15_pv_L0.
Module C_UW_52944_1bf85_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_1bf85_w7_r14_pP_L0.
Module C_UW_52944_1bf85_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_1bf85_w8_r15_pv_L0.
Module C_UW_52944_37acd_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_37acd_w7_r14_pP_L0.
Module C_UW_52944_37acd_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_37acd_w8_r15_pv_L0.
Module C_UW_52944_86df0_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_86df0_w6_r13_pP_L0.
Module C_UW_52944_86df0_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_86df0_w7_r14_pP_L0.
Module C_UW_52944_b60e4_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_b60e4_w7_r14_pP_L0.
Module C_UW_52944_b60e4_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_b60e4_w8_r15_pv_L0.
Module C_UW_52944_c350b_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_c350b_w6_r13_pP_L0.
Module C_UW_52944_c350b_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_c350b_w7_r14_pP_L0.
Module C_XA_22594_7b220_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_7b220_blk_w7_r14_L0.
Module C_XA_22594_7b220_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_7b220_p682f0_w6_r13_pP.
Module C_XA_22a78_d91f1_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_22a78_d91f1_blk_w7_r14_L0.
Module C_XA_22a78_d91f1_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_22a78_d91f1_p682f0_w6_r13_pP.
Module C_XA_52944_1bf85_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_1bf85_blk_w8_r15_L0.
Module C_XA_52944_1bf85_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_1bf85_p682f0_w7_r14_pP.
Module C_XA_52944_37acd_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_37acd_blk_w8_r15_L0.
Module C_XA_52944_37acd_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_37acd_p682f0_w7_r14_pP.
Module C_XA_52944_86df0_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_86df0_blk_w7_r14_L0.
Module C_XA_52944_86df0_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_86df0_p68250_w6_r13_pP.
Module C_XA_52944_b60e4_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_b60e4_blk_w8_r15_L0.
Module C_XA_52944_b60e4_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_b60e4_p682f0_w7_r14_pP.
Module C_XA_52944_c350b_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_c350b_blk_w7_r14_L0.
Module C_XA_52944_c350b_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_c350b_p68250_w6_r13_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4 Ubs_u_5.LibRunUbs_u_5 Ubs_u_6.LibRunUbs_u_6 Ubs_u_7.LibRunUbs_u_7 Ubs_u_8.LibRunUbs_u_8 Ubs_u_9.LibRunUbs_u_9 Ubs_u_10.LibRunUbs_u_10.

Module LibRunUbs_u_11.
Lemma LN_TUE_T_UW_52944_1bf85_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_1bf85_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_1bf85_w8_r15_pv_L0.CTX C_UW_52944_1bf85_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_1bf85_w8_r15_pv_L0) C_UW_52944_1bf85_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_1bf85_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_1bf85_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_1bf85_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_1bf85_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_1bf85_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_1bf85_blk_w8_r15_L0.CTX C_XA_52944_1bf85_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_1bf85_blk_w8_r15_L0) C_XA_52944_1bf85_blk_w8_r15_L0.OBLS [(497%uint63, T_Ubs2UE.T_UW_52944_1bf85_w8_r15_pv_L0)] C_XA_52944_1bf85_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_1bf85_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_1bf85_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_1bf85_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_1bf85_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_1bf85_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_1bf85_w7_r14_pP_L0.CTX C_UW_52944_1bf85_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_1bf85_w7_r14_pP_L0) C_UW_52944_1bf85_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_1bf85_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_1bf85_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_1bf85_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_1bf85_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_1bf85_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_1bf85_p682f0_w7_r14_pP.CTX C_XA_52944_1bf85_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_1bf85_p682f0_w7_r14_pP) C_XA_52944_1bf85_p682f0_w7_r14_pP.OBLS [(496%uint63, T_Ubs2UE.T_UW_52944_1bf85_w7_r14_pP_L0)] C_XA_52944_1bf85_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_1bf85_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_1bf85_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_1bf85_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1) C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.OBLS [(412%uint63, T_Ubs2UE.T_XA_52944_1bf85_blk_w8_r15_L0); (413%uint63, T_Ubs2UE.T_XA_52944_1bf85_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_1bf85_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_1bf85_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_7b220_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_7b220_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_7b220_w8_r15_pv_L0.CTX C_UW_22594_7b220_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_7b220_w8_r15_pv_L0) C_UW_22594_7b220_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22594_7b220_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_7b220_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_7b220_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_7b220_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_7b220_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_7b220_blk_w7_r14_L0.CTX C_XA_22594_7b220_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22594_7b220_blk_w7_r14_L0) C_XA_22594_7b220_blk_w7_r14_L0.OBLS [(252%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1); (315%uint63, T_Ubs2UE.T_UW_22594_7b220_w8_r15_pv_L0)] C_XA_22594_7b220_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_7b220_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_7b220_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_7b220_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_7b220_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_c350b_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_c350b_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_c350b_w7_r14_pP_L0.CTX C_UW_52944_c350b_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_c350b_w7_r14_pP_L0) C_UW_52944_c350b_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_c350b_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_c350b_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_c350b_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_c350b_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_c350b_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_c350b_blk_w7_r14_L0.CTX C_XA_52944_c350b_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_c350b_blk_w7_r14_L0) C_XA_52944_c350b_blk_w7_r14_L0.OBLS [(553%uint63, T_Ubs2UE.T_UW_52944_c350b_w7_r14_pP_L0)] C_XA_52944_c350b_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_c350b_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_c350b_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_c350b_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_c350b_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_c350b_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_c350b_w6_r13_pP_L0.CTX C_UW_52944_c350b_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_c350b_w6_r13_pP_L0) C_UW_52944_c350b_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_c350b_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_c350b_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_c350b_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_c350b_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_c350b_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_c350b_p68250_w6_r13_pP.CTX C_XA_52944_c350b_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_c350b_p68250_w6_r13_pP) C_XA_52944_c350b_p68250_w6_r13_pP.OBLS [(552%uint63, T_Ubs2UE.T_UW_52944_c350b_w6_r13_pP_L0)] C_XA_52944_c350b_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_c350b_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_c350b_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_c350b_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.OBLS [(468%uint63, T_Ubs2UE.T_XA_52944_c350b_blk_w7_r14_L0); (469%uint63, T_Ubs2UE.T_XA_52944_c350b_p68250_w6_r13_pP)] C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_c350b_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_c350b_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_7b220_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_7b220_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_7b220_w7_r14_pP_L0.CTX C_UW_22594_7b220_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_7b220_w7_r14_pP_L0) C_UW_22594_7b220_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22594_7b220_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_7b220_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_7b220_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_7b220_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_7b220_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_7b220_p682f0_w6_r13_pP.CTX C_XA_22594_7b220_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22594_7b220_p682f0_w6_r13_pP) C_XA_22594_7b220_p682f0_w6_r13_pP.OBLS [(253%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1); (314%uint63, T_Ubs2UE.T_UW_22594_7b220_w7_r14_pP_L0)] C_XA_22594_7b220_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_7b220_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_7b220_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_7b220_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_7b220_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.CTX C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1) C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.OBLS [(142%uint63, T_Ubs2UE.T_XA_22594_7b220_blk_w7_r14_L0); (143%uint63, T_Ubs2UE.T_XA_22594_7b220_p682f0_w6_r13_pP)] C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.CTX (@h_ctabUE _ _ _ H)) C_EH_22594_s10_m5_w6_r13_pv_L0_fc6bbf1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22594_7b220_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22594_7b220_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.CTX C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.PLAN (t_st T_Ubs2U.T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.OBLS [(222%uint63, T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1)] C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_fc6bbf1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22594_s10_m5_w6_r13_pv_L0_fc6bbf1 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.CTX C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.PLAN (t_st T_Ubs2U.T_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f) C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.OBLS [(147%uint63, T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f)] C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f22463f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.CTX C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.PLAN (t_st T_Ubs2U.T_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586) C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.OBLS [(148%uint63, T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586)] C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a3c_s10_m1_w7_r14_pv_L0_f09c586.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_b60e4_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_b60e4_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_b60e4_w8_r15_pv_L0.CTX C_UW_52944_b60e4_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_b60e4_w8_r15_pv_L0) C_UW_52944_b60e4_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_b60e4_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_b60e4_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_b60e4_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_b60e4_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_b60e4_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_b60e4_blk_w8_r15_L0.CTX C_XA_52944_b60e4_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_b60e4_blk_w8_r15_L0) C_XA_52944_b60e4_blk_w8_r15_L0.OBLS [(551%uint63, T_Ubs2UE.T_UW_52944_b60e4_w8_r15_pv_L0)] C_XA_52944_b60e4_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_b60e4_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_b60e4_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_b60e4_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_b60e4_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_b60e4_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_b60e4_w7_r14_pP_L0.CTX C_UW_52944_b60e4_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_b60e4_w7_r14_pP_L0) C_UW_52944_b60e4_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_b60e4_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_b60e4_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_b60e4_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_b60e4_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_b60e4_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_b60e4_p682f0_w7_r14_pP.CTX C_XA_52944_b60e4_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_b60e4_p682f0_w7_r14_pP) C_XA_52944_b60e4_p682f0_w7_r14_pP.OBLS [(550%uint63, T_Ubs2UE.T_UW_52944_b60e4_w7_r14_pP_L0)] C_XA_52944_b60e4_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_b60e4_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_b60e4_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_b60e4_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1) C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.OBLS [(466%uint63, T_Ubs2UE.T_XA_52944_b60e4_blk_w8_r15_L0); (467%uint63, T_Ubs2UE.T_XA_52944_b60e4_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_b60e4_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_b60e4_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_d91f1_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_d91f1_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_d91f1_w8_r15_pv_L0.CTX C_UW_22a78_d91f1_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_d91f1_w8_r15_pv_L0) C_UW_22a78_d91f1_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22a78_d91f1_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_d91f1_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_d91f1_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a78_d91f1_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a78_d91f1_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a78_d91f1_blk_w7_r14_L0.CTX C_XA_22a78_d91f1_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22a78_d91f1_blk_w7_r14_L0) C_XA_22a78_d91f1_blk_w7_r14_L0.OBLS [(268%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1); (331%uint63, T_Ubs2UE.T_UW_22a78_d91f1_w8_r15_pv_L0)] C_XA_22a78_d91f1_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a78_d91f1_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22a78_d91f1_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a78_d91f1_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a78_d91f1_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_86df0_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_86df0_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_86df0_w7_r14_pP_L0.CTX C_UW_52944_86df0_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_86df0_w7_r14_pP_L0) C_UW_52944_86df0_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_86df0_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_86df0_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_86df0_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_86df0_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_86df0_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_86df0_blk_w7_r14_L0.CTX C_XA_52944_86df0_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_86df0_blk_w7_r14_L0) C_XA_52944_86df0_blk_w7_r14_L0.OBLS [(537%uint63, T_Ubs2UE.T_UW_52944_86df0_w7_r14_pP_L0)] C_XA_52944_86df0_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_86df0_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_86df0_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_86df0_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_86df0_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_86df0_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_86df0_w6_r13_pP_L0.CTX C_UW_52944_86df0_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_86df0_w6_r13_pP_L0) C_UW_52944_86df0_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_86df0_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_86df0_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_86df0_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_86df0_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_86df0_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_86df0_p68250_w6_r13_pP.CTX C_XA_52944_86df0_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_86df0_p68250_w6_r13_pP) C_XA_52944_86df0_p68250_w6_r13_pP.OBLS [(536%uint63, T_Ubs2UE.T_UW_52944_86df0_w6_r13_pP_L0)] C_XA_52944_86df0_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_86df0_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_86df0_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_86df0_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.OBLS [(452%uint63, T_Ubs2UE.T_XA_52944_86df0_blk_w7_r14_L0); (453%uint63, T_Ubs2UE.T_XA_52944_86df0_p68250_w6_r13_pP)] C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_86df0_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_86df0_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_d91f1_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_d91f1_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_d91f1_w7_r14_pP_L0.CTX C_UW_22a78_d91f1_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_d91f1_w7_r14_pP_L0) C_UW_22a78_d91f1_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22a78_d91f1_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_d91f1_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_d91f1_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a78_d91f1_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a78_d91f1_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a78_d91f1_p682f0_w6_r13_pP.CTX C_XA_22a78_d91f1_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22a78_d91f1_p682f0_w6_r13_pP) C_XA_22a78_d91f1_p682f0_w6_r13_pP.OBLS [(269%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1); (330%uint63, T_Ubs2UE.T_UW_22a78_d91f1_w7_r14_pP_L0)] C_XA_22a78_d91f1_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a78_d91f1_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22a78_d91f1_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a78_d91f1_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a78_d91f1_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.CTX C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.PLAN (t_st T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539) C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.OBLS [(158%uint63, T_Ubs2UE.T_XA_22a78_d91f1_blk_w7_r14_L0); (159%uint63, T_Ubs2UE.T_XA_22a78_d91f1_p682f0_w6_r13_pP)] C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.CTX (@h_ctabUE _ _ _ H)) C_EH_22a78_s10_m5_w6_r13_pv_L0_f602539.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22a78_d91f1_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22a78_d91f1_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.CTX C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.PLAN (t_st T_Ubs2U.T_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.OBLS [(223%uint63, T_Ubs2U.T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539)] C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a78_s10_m1_w7_r14_pv_L0_f602539.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a78_s10_m5_w6_r13_pv_L0_f602539 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_37acd_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_37acd_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_37acd_w8_r15_pv_L0.CTX C_UW_52944_37acd_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_37acd_w8_r15_pv_L0) C_UW_52944_37acd_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_37acd_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_37acd_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_37acd_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_37acd_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_37acd_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_37acd_blk_w8_r15_L0.CTX C_XA_52944_37acd_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_37acd_blk_w8_r15_L0) C_XA_52944_37acd_blk_w8_r15_L0.OBLS [(511%uint63, T_Ubs2UE.T_UW_52944_37acd_w8_r15_pv_L0)] C_XA_52944_37acd_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_37acd_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_37acd_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_37acd_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_37acd_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_37acd_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_37acd_w7_r14_pP_L0.CTX C_UW_52944_37acd_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_37acd_w7_r14_pP_L0) C_UW_52944_37acd_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_37acd_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_37acd_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_37acd_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_37acd_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_37acd_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_37acd_p682f0_w7_r14_pP.CTX C_XA_52944_37acd_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_37acd_p682f0_w7_r14_pP) C_XA_52944_37acd_p682f0_w7_r14_pP.OBLS [(510%uint63, T_Ubs2UE.T_UW_52944_37acd_w7_r14_pP_L0)] C_XA_52944_37acd_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_37acd_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_37acd_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_37acd_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1) C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.OBLS [(426%uint63, T_Ubs2UE.T_XA_52944_37acd_blk_w8_r15_L0); (427%uint63, T_Ubs2UE.T_XA_52944_37acd_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a78_515a8_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_37acd_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_37acd_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a78_515a8_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a78_515a8_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a78_515a8_w8_r15_pv_L0.CTX C_UW_22a78_515a8_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22a78_515a8_w8_r15_pv_L0) C_UW_22a78_515a8_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22a78_515a8_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a78_515a8_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a78_515a8_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_11.
