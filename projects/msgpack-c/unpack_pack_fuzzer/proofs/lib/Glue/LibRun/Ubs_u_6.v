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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_03 B_05 B_09 B_10 B_12 B_15.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.
Module C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.
Module C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.
Module C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.
Module C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.
Module C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.
Module C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.
Module C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.
Module C_UW_22558_fe93b_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22558_fe93b_w7_r14_pP_L0.
Module C_UW_22a3c_e2130_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a3c_e2130_w7_r14_pP_L0.
Module C_UW_22a3c_e2130_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a3c_e2130_w8_r15_pv_L0.
Module C_UW_22a3c_ed69c_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a3c_ed69c_w7_r14_pP_L0.
Module C_UW_22a3c_ed69c_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22a3c_ed69c_w8_r15_pv_L0.
Module C_UW_52944_14888_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_14888_w7_r14_pP_L0.
Module C_UW_52944_14888_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_14888_w8_r15_pv_L0.
Module C_UW_52944_1da74_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_1da74_w6_r13_pP_L0.
Module C_UW_52944_1da74_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_UW_52944_1da74_w7_r14_pP_L0.
Module C_UW_52944_4716c_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_12.C_UW_52944_4716c_w6_r13_pP_L0.
Module C_UW_52944_4716c_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_12.C_UW_52944_4716c_w7_r14_pP_L0.
Module C_UW_52944_daf78_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_daf78_w6_r13_pP_L0.
Module C_UW_52944_daf78_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_daf78_w7_r14_pP_L0.
Module C_UW_52944_e1561_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_e1561_w7_r14_pP_L0.
Module C_UW_52944_e1561_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_e1561_w8_r15_pv_L0.
Module C_XA_22558_fe93b_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22558_fe93b_p682f0_w6_r13_pP.
Module C_XA_22a3c_e2130_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22a3c_e2130_blk_w7_r14_L0.
Module C_XA_22a3c_e2130_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22a3c_e2130_p682f0_w6_r13_pP.
Module C_XA_22a3c_ed69c_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22a3c_ed69c_blk_w7_r14_L0.
Module C_XA_22a3c_ed69c_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22a3c_ed69c_p682f0_w6_r13_pP.
Module C_XA_52944_14888_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_14888_blk_w8_r15_L0.
Module C_XA_52944_14888_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_14888_p682f0_w7_r14_pP.
Module C_XA_52944_1da74_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_1da74_blk_w7_r14_L0.
Module C_XA_52944_1da74_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_1da74_p68250_w6_r13_pP.
Module C_XA_52944_4716c_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_4716c_blk_w7_r14_L0.
Module C_XA_52944_4716c_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_4716c_p68250_w6_r13_pP.
Module C_XA_52944_daf78_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_daf78_blk_w7_r14_L0.
Module C_XA_52944_daf78_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_daf78_p68250_w6_r13_pP.
Module C_XA_52944_e1561_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_e1561_blk_w8_r15_L0.
Module C_XA_52944_e1561_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_e1561_p682f0_w7_r14_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4 Ubs_u_5.LibRunUbs_u_5.

Module LibRunUbs_u_6.
Lemma LN_TUE_T_UW_52944_1da74_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_1da74_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_1da74_w7_r14_pP_L0.CTX C_UW_52944_1da74_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_1da74_w7_r14_pP_L0) C_UW_52944_1da74_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_1da74_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_1da74_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_1da74_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_1da74_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_1da74_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_1da74_blk_w7_r14_L0.CTX C_XA_52944_1da74_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_1da74_blk_w7_r14_L0) C_XA_52944_1da74_blk_w7_r14_L0.OBLS [(499%uint63, T_Ubs2UE.T_UW_52944_1da74_w7_r14_pP_L0)] C_XA_52944_1da74_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_1da74_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_1da74_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_1da74_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_1da74_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_1da74_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_1da74_w6_r13_pP_L0.CTX C_UW_52944_1da74_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_1da74_w6_r13_pP_L0) C_UW_52944_1da74_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_1da74_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_1da74_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_1da74_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_1da74_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_1da74_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_1da74_p68250_w6_r13_pP.CTX C_XA_52944_1da74_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_1da74_p68250_w6_r13_pP) C_XA_52944_1da74_p68250_w6_r13_pP.OBLS [(498%uint63, T_Ubs2UE.T_UW_52944_1da74_w6_r13_pP_L0)] C_XA_52944_1da74_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_1da74_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_1da74_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_1da74_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.OBLS [(414%uint63, T_Ubs2UE.T_XA_52944_1da74_blk_w7_r14_L0); (415%uint63, T_Ubs2UE.T_XA_52944_1da74_p68250_w6_r13_pP)] C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_1da74_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_1da74_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22558_fe93b_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22558_fe93b_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22558_fe93b_w7_r14_pP_L0.CTX C_UW_22558_fe93b_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22558_fe93b_w7_r14_pP_L0) C_UW_22558_fe93b_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22558_fe93b_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22558_fe93b_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22558_fe93b_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22558_fe93b_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22558_fe93b_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22558_fe93b_p682f0_w6_r13_pP.CTX C_XA_22558_fe93b_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22558_fe93b_p682f0_w6_r13_pP) C_XA_22558_fe93b_p682f0_w6_r13_pP.OBLS [(245%uint63, T_Ubs2UE.T_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1); (306%uint63, T_Ubs2UE.T_UW_22558_fe93b_w7_r14_pP_L0)] C_XA_22558_fe93b_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22558_fe93b_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22558_fe93b_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22558_fe93b_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22558_fe93b_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.CTX C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.PLAN (t_st T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4) C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.OBLS [(134%uint63, T_Ubs2UE.T_XA_22558_fe93b_blk_w7_r14_L0); (135%uint63, T_Ubs2UE.T_XA_22558_fe93b_p682f0_w6_r13_pP)] C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.CTX (@h_ctabUE _ _ _ H)) C_EH_22558_s10_m5_w6_r13_pv_L0_fc741c4.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22558_fe93b_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22558_fe93b_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.CTX C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.PLAN (t_st T_Ubs2U.T_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4) C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.OBLS [(146%uint63, T_Ubs2U.T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4)] C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22558_s10_m1_w5_r12_pv_L0_fc741c4.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22558_s10_m5_w6_r13_pv_L0_fc741c4 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_14888_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_14888_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_14888_w8_r15_pv_L0.CTX C_UW_52944_14888_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_14888_w8_r15_pv_L0) C_UW_52944_14888_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_14888_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_14888_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_14888_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_14888_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_14888_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_14888_blk_w8_r15_L0.CTX C_XA_52944_14888_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_14888_blk_w8_r15_L0) C_XA_52944_14888_blk_w8_r15_L0.OBLS [(495%uint63, T_Ubs2UE.T_UW_52944_14888_w8_r15_pv_L0)] C_XA_52944_14888_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_14888_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_14888_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_14888_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_14888_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_14888_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_14888_w7_r14_pP_L0.CTX C_UW_52944_14888_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_14888_w7_r14_pP_L0) C_UW_52944_14888_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_14888_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_14888_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_14888_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_14888_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_14888_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_14888_p682f0_w7_r14_pP.CTX C_XA_52944_14888_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_14888_p682f0_w7_r14_pP) C_XA_52944_14888_p682f0_w7_r14_pP.OBLS [(494%uint63, T_Ubs2UE.T_UW_52944_14888_w7_r14_pP_L0)] C_XA_52944_14888_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_14888_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_14888_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_14888_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1) C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.OBLS [(410%uint63, T_Ubs2UE.T_XA_52944_14888_blk_w8_r15_L0); (411%uint63, T_Ubs2UE.T_XA_52944_14888_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_14888_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_14888_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a3c_e2130_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a3c_e2130_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a3c_e2130_w8_r15_pv_L0.CTX C_UW_22a3c_e2130_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22a3c_e2130_w8_r15_pv_L0) C_UW_22a3c_e2130_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22a3c_e2130_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a3c_e2130_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a3c_e2130_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a3c_e2130_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a3c_e2130_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a3c_e2130_blk_w7_r14_L0.CTX C_XA_22a3c_e2130_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22a3c_e2130_blk_w7_r14_L0) C_XA_22a3c_e2130_blk_w7_r14_L0.OBLS [(258%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1); (321%uint63, T_Ubs2UE.T_UW_22a3c_e2130_w8_r15_pv_L0)] C_XA_22a3c_e2130_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a3c_e2130_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22a3c_e2130_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a3c_e2130_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a3c_e2130_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_daf78_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_daf78_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_daf78_w7_r14_pP_L0.CTX C_UW_52944_daf78_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_daf78_w7_r14_pP_L0) C_UW_52944_daf78_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_daf78_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_daf78_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_daf78_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_daf78_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_daf78_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_daf78_blk_w7_r14_L0.CTX C_XA_52944_daf78_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_daf78_blk_w7_r14_L0) C_XA_52944_daf78_blk_w7_r14_L0.OBLS [(563%uint63, T_Ubs2UE.T_UW_52944_daf78_w7_r14_pP_L0)] C_XA_52944_daf78_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_daf78_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_daf78_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_daf78_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_daf78_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_daf78_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_daf78_w6_r13_pP_L0.CTX C_UW_52944_daf78_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_daf78_w6_r13_pP_L0) C_UW_52944_daf78_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_daf78_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_daf78_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_daf78_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_daf78_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_daf78_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_daf78_p68250_w6_r13_pP.CTX C_XA_52944_daf78_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_daf78_p68250_w6_r13_pP) C_XA_52944_daf78_p68250_w6_r13_pP.OBLS [(562%uint63, T_Ubs2UE.T_UW_52944_daf78_w6_r13_pP_L0)] C_XA_52944_daf78_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_daf78_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_daf78_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_daf78_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.OBLS [(478%uint63, T_Ubs2UE.T_XA_52944_daf78_blk_w7_r14_L0); (479%uint63, T_Ubs2UE.T_XA_52944_daf78_p68250_w6_r13_pP)] C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_daf78_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_daf78_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a3c_e2130_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a3c_e2130_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a3c_e2130_w7_r14_pP_L0.CTX C_UW_22a3c_e2130_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22a3c_e2130_w7_r14_pP_L0) C_UW_22a3c_e2130_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22a3c_e2130_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a3c_e2130_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a3c_e2130_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a3c_e2130_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a3c_e2130_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a3c_e2130_p682f0_w6_r13_pP.CTX C_XA_22a3c_e2130_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22a3c_e2130_p682f0_w6_r13_pP) C_XA_22a3c_e2130_p682f0_w6_r13_pP.OBLS [(259%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1); (320%uint63, T_Ubs2UE.T_UW_22a3c_e2130_w7_r14_pP_L0)] C_XA_22a3c_e2130_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a3c_e2130_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22a3c_e2130_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a3c_e2130_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a3c_e2130_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.CTX C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.PLAN (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f) C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.OBLS [(148%uint63, T_Ubs2UE.T_XA_22a3c_e2130_blk_w7_r14_L0); (149%uint63, T_Ubs2UE.T_XA_22a3c_e2130_p682f0_w6_r13_pP)] C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.CTX (@h_ctabUE _ _ _ H)) C_EH_22a3c_s10_m5_w6_r13_pv_L0_f22463f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22a3c_e2130_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22a3c_e2130_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.CTX C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.PLAN (t_st T_Ubs2U.T_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f) C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.OBLS [(147%uint63, T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f)] C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22a3c_s10_m1_w5_r12_pv_L0_f22463f.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f22463f _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_e1561_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_e1561_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_e1561_w8_r15_pv_L0.CTX C_UW_52944_e1561_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_e1561_w8_r15_pv_L0) C_UW_52944_e1561_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_e1561_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_e1561_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_e1561_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_e1561_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_e1561_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_e1561_blk_w8_r15_L0.CTX C_XA_52944_e1561_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_e1561_blk_w8_r15_L0) C_XA_52944_e1561_blk_w8_r15_L0.OBLS [(567%uint63, T_Ubs2UE.T_UW_52944_e1561_w8_r15_pv_L0)] C_XA_52944_e1561_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_e1561_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_e1561_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_e1561_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_e1561_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_e1561_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_e1561_w7_r14_pP_L0.CTX C_UW_52944_e1561_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_e1561_w7_r14_pP_L0) C_UW_52944_e1561_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_e1561_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_e1561_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_e1561_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_e1561_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_e1561_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_e1561_p682f0_w7_r14_pP.CTX C_XA_52944_e1561_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_e1561_p682f0_w7_r14_pP) C_XA_52944_e1561_p682f0_w7_r14_pP.OBLS [(566%uint63, T_Ubs2UE.T_UW_52944_e1561_w7_r14_pP_L0)] C_XA_52944_e1561_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_e1561_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_e1561_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_e1561_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1) C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.OBLS [(482%uint63, T_Ubs2UE.T_XA_52944_e1561_blk_w8_r15_L0); (483%uint63, T_Ubs2UE.T_XA_52944_e1561_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_e1561_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_e1561_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a3c_ed69c_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a3c_ed69c_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a3c_ed69c_w8_r15_pv_L0.CTX C_UW_22a3c_ed69c_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22a3c_ed69c_w8_r15_pv_L0) C_UW_22a3c_ed69c_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22a3c_ed69c_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a3c_ed69c_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a3c_ed69c_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a3c_ed69c_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a3c_ed69c_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a3c_ed69c_blk_w7_r14_L0.CTX C_XA_22a3c_ed69c_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22a3c_ed69c_blk_w7_r14_L0) C_XA_22a3c_ed69c_blk_w7_r14_L0.OBLS [(260%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1); (323%uint63, T_Ubs2UE.T_UW_22a3c_ed69c_w8_r15_pv_L0)] C_XA_22a3c_ed69c_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a3c_ed69c_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22a3c_ed69c_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a3c_ed69c_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a3c_ed69c_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_4716c_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_4716c_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_4716c_w7_r14_pP_L0.CTX C_UW_52944_4716c_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_4716c_w7_r14_pP_L0) C_UW_52944_4716c_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_4716c_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_4716c_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_4716c_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_4716c_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_4716c_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_4716c_blk_w7_r14_L0.CTX C_XA_52944_4716c_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_4716c_blk_w7_r14_L0) C_XA_52944_4716c_blk_w7_r14_L0.OBLS [(517%uint63, T_Ubs2UE.T_UW_52944_4716c_w7_r14_pP_L0)] C_XA_52944_4716c_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_4716c_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_4716c_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_4716c_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_4716c_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_4716c_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_4716c_w6_r13_pP_L0.CTX C_UW_52944_4716c_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_4716c_w6_r13_pP_L0) C_UW_52944_4716c_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_4716c_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_4716c_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_4716c_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_4716c_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_4716c_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_4716c_p68250_w6_r13_pP.CTX C_XA_52944_4716c_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_4716c_p68250_w6_r13_pP) C_XA_52944_4716c_p68250_w6_r13_pP.OBLS [(516%uint63, T_Ubs2UE.T_UW_52944_4716c_w6_r13_pP_L0)] C_XA_52944_4716c_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_4716c_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_4716c_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_4716c_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.OBLS [(432%uint63, T_Ubs2UE.T_XA_52944_4716c_blk_w7_r14_L0); (433%uint63, T_Ubs2UE.T_XA_52944_4716c_p68250_w6_r13_pP)] C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_4716c_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_4716c_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22a3c_ed69c_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22a3c_ed69c_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22a3c_ed69c_w7_r14_pP_L0.CTX C_UW_22a3c_ed69c_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22a3c_ed69c_w7_r14_pP_L0) C_UW_22a3c_ed69c_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22a3c_ed69c_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22a3c_ed69c_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22a3c_ed69c_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22a3c_ed69c_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22a3c_ed69c_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22a3c_ed69c_p682f0_w6_r13_pP.CTX C_XA_22a3c_ed69c_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22a3c_ed69c_p682f0_w6_r13_pP) C_XA_22a3c_ed69c_p682f0_w6_r13_pP.OBLS [(261%uint63, T_Ubs2UE.T_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1); (322%uint63, T_Ubs2UE.T_UW_22a3c_ed69c_w7_r14_pP_L0)] C_XA_22a3c_ed69c_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22a3c_ed69c_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22a3c_ed69c_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22a3c_ed69c_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22a3c_ed69c_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.CTX C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.PLAN (t_st T_Ubs2U.T_THROW_22a3c_s10_m5_w6_r13_pv_L0_f09c586) C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.OBLS [(150%uint63, T_Ubs2UE.T_XA_22a3c_ed69c_blk_w7_r14_L0); (151%uint63, T_Ubs2UE.T_XA_22a3c_ed69c_p682f0_w6_r13_pP)] C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.CTX (@h_ctabUE _ _ _ H)) C_EH_22a3c_s10_m5_w6_r13_pv_L0_f09c586.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22a3c_ed69c_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22a3c_ed69c_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_6.
