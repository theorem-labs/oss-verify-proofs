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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_03 B_05 B_09 B_10 B_11 B_12 B_14 B_15.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3 Ubs_u_4 Ubs_u_5 Ubs_u_6 Ubs_u_7 Ubs_u_8.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.
Module C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.
Module C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.
Module C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.
Module C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.
Module C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.
Module C_UW_22594_02d0c_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_02d0c_w7_r14_pP_L0.
Module C_UW_22594_02d0c_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_02d0c_w8_r15_pv_L0.
Module C_UW_22594_738a4_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_738a4_w8_r15_pv_L0.
Module C_UW_22594_994b7_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_994b7_w7_r14_pP_L0.
Module C_UW_22594_994b7_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_22594_994b7_w8_r15_pv_L0.
Module C_UW_52944_22bfb_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_22bfb_w7_r14_pP_L0.
Module C_UW_52944_22bfb_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_22bfb_w8_r15_pv_L0.
Module C_UW_52944_354ca_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_11.C_UW_52944_354ca_w7_r14_pP_L0.
Module C_UW_52944_6cd6d_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_12.C_UW_52944_6cd6d_w7_r14_pP_L0.
Module C_UW_52944_6cd6d_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_12.C_UW_52944_6cd6d_w8_r15_pv_L0.
Module C_UW_52944_9fb12_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_9fb12_w6_r13_pP_L0.
Module C_UW_52944_9fb12_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_9fb12_w7_r14_pP_L0.
Module C_UW_52944_d3ed2_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_d3ed2_w7_r14_pP_L0.
Module C_UW_52944_d3ed2_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_d3ed2_w8_r15_pv_L0.
Module C_UW_52944_dcf48_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_dcf48_w6_r13_pP_L0.
Module C_UW_52944_dcf48_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_dcf48_w7_r14_pP_L0.
Module C_XA_22594_02d0c_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_02d0c_blk_w7_r14_L0.
Module C_XA_22594_02d0c_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_02d0c_p682f0_w6_r13_pP.
Module C_XA_22594_738a4_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_738a4_blk_w7_r14_L0.
Module C_XA_22594_994b7_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_994b7_blk_w7_r14_L0.
Module C_XA_22594_994b7_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_22594_994b7_p682f0_w6_r13_pP.
Module C_XA_52944_22bfb_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_22bfb_blk_w8_r15_L0.
Module C_XA_52944_22bfb_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_22bfb_p682f0_w7_r14_pP.
Module C_XA_52944_6cd6d_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_6cd6d_blk_w8_r15_L0.
Module C_XA_52944_6cd6d_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_6cd6d_p682f0_w7_r14_pP.
Module C_XA_52944_9fb12_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_9fb12_blk_w7_r14_L0.
Module C_XA_52944_9fb12_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_9fb12_p68250_w6_r13_pP.
Module C_XA_52944_d3ed2_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_d3ed2_blk_w8_r15_L0.
Module C_XA_52944_d3ed2_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_d3ed2_p682f0_w7_r14_pP.
Module C_XA_52944_dcf48_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_dcf48_blk_w7_r14_L0.
Module C_XA_52944_dcf48_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_dcf48_p68250_w6_r13_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3 Ubs_u_4.LibRunUbs_u_4 Ubs_u_5.LibRunUbs_u_5 Ubs_u_6.LibRunUbs_u_6 Ubs_u_7.LibRunUbs_u_7 Ubs_u_8.LibRunUbs_u_8.

Module LibRunUbs_u_9.
Lemma LN_TUE_T_UW_52944_d3ed2_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_d3ed2_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_d3ed2_w8_r15_pv_L0.CTX C_UW_52944_d3ed2_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_d3ed2_w8_r15_pv_L0) C_UW_52944_d3ed2_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_d3ed2_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_d3ed2_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_d3ed2_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_d3ed2_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_d3ed2_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_d3ed2_blk_w8_r15_L0.CTX C_XA_52944_d3ed2_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_d3ed2_blk_w8_r15_L0) C_XA_52944_d3ed2_blk_w8_r15_L0.OBLS [(561%uint63, T_Ubs2UE.T_UW_52944_d3ed2_w8_r15_pv_L0)] C_XA_52944_d3ed2_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_d3ed2_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_d3ed2_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_d3ed2_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_d3ed2_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_d3ed2_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_d3ed2_w7_r14_pP_L0.CTX C_UW_52944_d3ed2_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_d3ed2_w7_r14_pP_L0) C_UW_52944_d3ed2_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_d3ed2_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_d3ed2_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_d3ed2_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_d3ed2_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_d3ed2_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_d3ed2_p682f0_w7_r14_pP.CTX C_XA_52944_d3ed2_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_d3ed2_p682f0_w7_r14_pP) C_XA_52944_d3ed2_p682f0_w7_r14_pP.OBLS [(560%uint63, T_Ubs2UE.T_UW_52944_d3ed2_w7_r14_pP_L0)] C_XA_52944_d3ed2_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_d3ed2_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_d3ed2_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_d3ed2_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1) C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.OBLS [(476%uint63, T_Ubs2UE.T_XA_52944_d3ed2_blk_w8_r15_L0); (477%uint63, T_Ubs2UE.T_XA_52944_d3ed2_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_d3ed2_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_d3ed2_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_02d0c_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_02d0c_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_02d0c_w8_r15_pv_L0.CTX C_UW_22594_02d0c_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_02d0c_w8_r15_pv_L0) C_UW_22594_02d0c_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22594_02d0c_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_02d0c_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_02d0c_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_02d0c_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_02d0c_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_02d0c_blk_w7_r14_L0.CTX C_XA_22594_02d0c_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22594_02d0c_blk_w7_r14_L0) C_XA_22594_02d0c_blk_w7_r14_L0.OBLS [(246%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1); (309%uint63, T_Ubs2UE.T_UW_22594_02d0c_w8_r15_pv_L0)] C_XA_22594_02d0c_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_02d0c_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_02d0c_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_02d0c_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_02d0c_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_dcf48_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_dcf48_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_dcf48_w7_r14_pP_L0.CTX C_UW_52944_dcf48_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_dcf48_w7_r14_pP_L0) C_UW_52944_dcf48_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_dcf48_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_dcf48_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_dcf48_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_dcf48_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_dcf48_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_dcf48_blk_w7_r14_L0.CTX C_XA_52944_dcf48_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_dcf48_blk_w7_r14_L0) C_XA_52944_dcf48_blk_w7_r14_L0.OBLS [(565%uint63, T_Ubs2UE.T_UW_52944_dcf48_w7_r14_pP_L0)] C_XA_52944_dcf48_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_dcf48_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_dcf48_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_dcf48_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_dcf48_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_dcf48_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_dcf48_w6_r13_pP_L0.CTX C_UW_52944_dcf48_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_dcf48_w6_r13_pP_L0) C_UW_52944_dcf48_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_dcf48_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_dcf48_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_dcf48_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_dcf48_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_dcf48_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_dcf48_p68250_w6_r13_pP.CTX C_XA_52944_dcf48_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_dcf48_p68250_w6_r13_pP) C_XA_52944_dcf48_p68250_w6_r13_pP.OBLS [(564%uint63, T_Ubs2UE.T_UW_52944_dcf48_w6_r13_pP_L0)] C_XA_52944_dcf48_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_dcf48_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_dcf48_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_dcf48_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.OBLS [(480%uint63, T_Ubs2UE.T_XA_52944_dcf48_blk_w7_r14_L0); (481%uint63, T_Ubs2UE.T_XA_52944_dcf48_p68250_w6_r13_pP)] C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_dcf48_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_dcf48_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_02d0c_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_02d0c_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_02d0c_w7_r14_pP_L0.CTX C_UW_22594_02d0c_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_02d0c_w7_r14_pP_L0) C_UW_22594_02d0c_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22594_02d0c_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_02d0c_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_02d0c_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_02d0c_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_02d0c_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_02d0c_p682f0_w6_r13_pP.CTX C_XA_22594_02d0c_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22594_02d0c_p682f0_w6_r13_pP) C_XA_22594_02d0c_p682f0_w6_r13_pP.OBLS [(247%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1); (308%uint63, T_Ubs2UE.T_UW_22594_02d0c_w7_r14_pP_L0)] C_XA_22594_02d0c_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_02d0c_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_02d0c_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_02d0c_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_02d0c_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.CTX C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d) C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.OBLS [(136%uint63, T_Ubs2UE.T_XA_22594_02d0c_blk_w7_r14_L0); (137%uint63, T_Ubs2UE.T_XA_22594_02d0c_p682f0_w6_r13_pP)] C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.CTX (@h_ctabUE _ _ _ H)) C_EH_22594_s10_m5_w6_r13_pv_L0_ffe383d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22594_02d0c_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22594_02d0c_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.CTX C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.PLAN (t_st T_Ubs2U.T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.OBLS [(217%uint63, T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d)] C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_ffe383d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22594_s10_m5_w6_r13_pv_L0_ffe383d _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_6cd6d_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_6cd6d_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_6cd6d_w8_r15_pv_L0.CTX C_UW_52944_6cd6d_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_6cd6d_w8_r15_pv_L0) C_UW_52944_6cd6d_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_6cd6d_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_6cd6d_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_6cd6d_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_6cd6d_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_6cd6d_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_6cd6d_blk_w8_r15_L0.CTX C_XA_52944_6cd6d_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_6cd6d_blk_w8_r15_L0) C_XA_52944_6cd6d_blk_w8_r15_L0.OBLS [(527%uint63, T_Ubs2UE.T_UW_52944_6cd6d_w8_r15_pv_L0)] C_XA_52944_6cd6d_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_6cd6d_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_6cd6d_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_6cd6d_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_6cd6d_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_6cd6d_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_6cd6d_w7_r14_pP_L0.CTX C_UW_52944_6cd6d_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_6cd6d_w7_r14_pP_L0) C_UW_52944_6cd6d_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_6cd6d_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_6cd6d_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_6cd6d_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_6cd6d_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_6cd6d_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_6cd6d_p682f0_w7_r14_pP.CTX C_XA_52944_6cd6d_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_6cd6d_p682f0_w7_r14_pP) C_XA_52944_6cd6d_p682f0_w7_r14_pP.OBLS [(526%uint63, T_Ubs2UE.T_UW_52944_6cd6d_w7_r14_pP_L0)] C_XA_52944_6cd6d_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_6cd6d_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_6cd6d_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_6cd6d_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1) C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.OBLS [(442%uint63, T_Ubs2UE.T_XA_52944_6cd6d_blk_w8_r15_L0); (443%uint63, T_Ubs2UE.T_XA_52944_6cd6d_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_6cd6d_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_6cd6d_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_994b7_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_994b7_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_994b7_w8_r15_pv_L0.CTX C_UW_22594_994b7_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_994b7_w8_r15_pv_L0) C_UW_22594_994b7_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22594_994b7_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_994b7_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_994b7_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_994b7_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_994b7_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_994b7_blk_w7_r14_L0.CTX C_XA_22594_994b7_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22594_994b7_blk_w7_r14_L0) C_XA_22594_994b7_blk_w7_r14_L0.OBLS [(256%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1); (319%uint63, T_Ubs2UE.T_UW_22594_994b7_w8_r15_pv_L0)] C_XA_22594_994b7_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_994b7_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_994b7_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_994b7_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_994b7_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_9fb12_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_9fb12_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_9fb12_w7_r14_pP_L0.CTX C_UW_52944_9fb12_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_9fb12_w7_r14_pP_L0) C_UW_52944_9fb12_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_9fb12_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_9fb12_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_9fb12_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_9fb12_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_9fb12_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_9fb12_blk_w7_r14_L0.CTX C_XA_52944_9fb12_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_9fb12_blk_w7_r14_L0) C_XA_52944_9fb12_blk_w7_r14_L0.OBLS [(545%uint63, T_Ubs2UE.T_UW_52944_9fb12_w7_r14_pP_L0)] C_XA_52944_9fb12_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_9fb12_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_9fb12_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_9fb12_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_9fb12_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_9fb12_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_9fb12_w6_r13_pP_L0.CTX C_UW_52944_9fb12_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_9fb12_w6_r13_pP_L0) C_UW_52944_9fb12_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_9fb12_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_9fb12_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_9fb12_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_9fb12_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_9fb12_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_9fb12_p68250_w6_r13_pP.CTX C_XA_52944_9fb12_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_9fb12_p68250_w6_r13_pP) C_XA_52944_9fb12_p68250_w6_r13_pP.OBLS [(544%uint63, T_Ubs2UE.T_UW_52944_9fb12_w6_r13_pP_L0)] C_XA_52944_9fb12_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_9fb12_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_9fb12_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_9fb12_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.OBLS [(460%uint63, T_Ubs2UE.T_XA_52944_9fb12_blk_w7_r14_L0); (461%uint63, T_Ubs2UE.T_XA_52944_9fb12_p68250_w6_r13_pP)] C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_9fb12_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_9fb12_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_994b7_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_994b7_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_994b7_w7_r14_pP_L0.CTX C_UW_22594_994b7_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_994b7_w7_r14_pP_L0) C_UW_22594_994b7_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_22594_994b7_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_994b7_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_994b7_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_994b7_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_994b7_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_994b7_p682f0_w6_r13_pP.CTX C_XA_22594_994b7_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_22594_994b7_p682f0_w6_r13_pP) C_XA_22594_994b7_p682f0_w6_r13_pP.OBLS [(257%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1); (318%uint63, T_Ubs2UE.T_UW_22594_994b7_w7_r14_pP_L0)] C_XA_22594_994b7_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_994b7_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_994b7_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_994b7_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_994b7_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.CTX C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.PLAN (t_st T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1) C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.OBLS [(146%uint63, T_Ubs2UE.T_XA_22594_994b7_blk_w7_r14_L0); (147%uint63, T_Ubs2UE.T_XA_22594_994b7_p682f0_w6_r13_pP)] C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.WF ITAB_ok (contracts_ok_of SEGS R C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.CTX (@h_ctabUE _ _ _ H)) C_EH_22594_s10_m5_w6_r13_pv_L0_f0112c1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_22594_994b7_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_22594_994b7_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.CTX C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.PLAN (t_st T_Ubs2U.T_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.OBLS [(218%uint63, T_Ubs2U.T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1)] C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_22594_s10_m1_w7_r14_pv_L0_f0112c1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_22594_s10_m5_w6_r13_pv_L0_f0112c1 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_22bfb_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_22bfb_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_22bfb_w8_r15_pv_L0.CTX C_UW_52944_22bfb_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_22bfb_w8_r15_pv_L0) C_UW_52944_22bfb_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_22bfb_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_22bfb_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_22bfb_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_22bfb_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_22bfb_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_22bfb_blk_w8_r15_L0.CTX C_XA_52944_22bfb_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_22bfb_blk_w8_r15_L0) C_XA_52944_22bfb_blk_w8_r15_L0.OBLS [(503%uint63, T_Ubs2UE.T_UW_52944_22bfb_w8_r15_pv_L0)] C_XA_52944_22bfb_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_22bfb_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_22bfb_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_22bfb_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_22bfb_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_22bfb_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_22bfb_w7_r14_pP_L0.CTX C_UW_52944_22bfb_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_22bfb_w7_r14_pP_L0) C_UW_52944_22bfb_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_22bfb_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_22bfb_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_22bfb_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_22bfb_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_22bfb_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_22bfb_p682f0_w7_r14_pP.CTX C_XA_52944_22bfb_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_22bfb_p682f0_w7_r14_pP) C_XA_52944_22bfb_p682f0_w7_r14_pP.OBLS [(502%uint63, T_Ubs2UE.T_UW_52944_22bfb_w7_r14_pP_L0)] C_XA_52944_22bfb_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_22bfb_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_22bfb_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_22bfb_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1) C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.OBLS [(418%uint63, T_Ubs2UE.T_XA_52944_22bfb_blk_w8_r15_L0); (419%uint63, T_Ubs2UE.T_XA_52944_22bfb_p682f0_w7_r14_pP)] C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_22bfb_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_22bfb_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_22594_738a4_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_22594_738a4_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_22594_738a4_w8_r15_pv_L0.CTX C_UW_22594_738a4_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_22594_738a4_w8_r15_pv_L0) C_UW_22594_738a4_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_22594_738a4_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_22594_738a4_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_22594_738a4_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_22594_738a4_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_22594_738a4_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_22594_738a4_blk_w7_r14_L0.CTX C_XA_22594_738a4_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_22594_738a4_blk_w7_r14_L0) C_XA_22594_738a4_blk_w7_r14_L0.OBLS [(250%uint63, T_Ubs2UE.T_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1); (313%uint63, T_Ubs2UE.T_UW_22594_738a4_w8_r15_pv_L0)] C_XA_22594_738a4_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_22594_738a4_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_22594_738a4_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_22594_738a4_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_22594_738a4_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_354ca_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_354ca_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_354ca_w7_r14_pP_L0.CTX C_UW_52944_354ca_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_354ca_w7_r14_pP_L0) C_UW_52944_354ca_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_354ca_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_354ca_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_354ca_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_9.
