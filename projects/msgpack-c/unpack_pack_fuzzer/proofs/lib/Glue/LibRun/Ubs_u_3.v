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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require B_00 B_01 B_02.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_02 B_03 B_06 B_07 B_08.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.
Module C_PKHEAD_m0k0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PKHEAD_m0k0.
Module C_PKHEAD_m1k0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKHEAD_m1k0.
Module C_PKHEAD_m1k1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PKHEAD_m1k1.
Module C_PKPOP_e_m0k0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKPOP_e_m0k0.
Module C_PKPOP_e_m1k0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKPOP_e_m1k0.
Module C_PKPOP_e_m1k1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKPOP_e_m1k1.
Module C_PKPOP_n_m0k0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKPOP_n_m0k0.
Module C_PKPOP_n_m0k0z := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PKPOP_n_m0k0z.
Module C_PKPOP_n_m1k0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKPOP_n_m1k0.
Module C_PKPOP_n_m1k1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PKPOP_n_m1k1.
Module C_PKPOP_n_m1k1z := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PKPOP_n_m1k1z.
Module C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.
Module C_UW_1f934_b775a_w4_r11_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_UW_1f934_b775a_w4_r11_pP_L0.
Module C_UW_1f934_b775a_w5_r12_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_UW_1f934_b775a_w5_r12_pv_L0.
Module C_UW_236d8_15ebf_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_15ebf_w6_r13_pP_L0.
Module C_UW_236d8_15ebf_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_15ebf_w7_r14_pv_L0.
Module C_UW_236d8_175a8_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_175a8_w6_r13_pP_L0.
Module C_UW_236d8_b5974_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_b5974_w6_r13_pP_L0.
Module C_UW_236d8_b5974_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_b5974_w7_r14_pv_L0.
Module C_UW_236d8_b649e_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_b649e_w6_r13_pP_L0.
Module C_UW_236d8_b649e_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_b649e_w7_r14_pv_L0.
Module C_UW_236d8_c7850_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_c7850_w6_r13_pP_L0.
Module C_UW_236d8_c7850_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_c7850_w7_r14_pv_L0.
Module C_UW_52944_73b21_w5_r12_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_73b21_w5_r12_pP_L0.
Module C_UW_52944_73b21_w6_r13_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_08.C_UW_52944_73b21_w6_r13_pv_L0.
Module C_XA_1f934_b775a_blk_w5_r12_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_1f934_b775a_blk_w5_r12_L0.
Module C_XA_1f934_b775a_p682f0_w4_r11_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_1f934_b775a_p682f0_w4_r11_pP.
Module C_XA_236d8_15ebf_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_15ebf_blk_w7_r14_L0.
Module C_XA_236d8_15ebf_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_15ebf_p682f0_w6_r13_pP.
Module C_XA_236d8_175a8_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_175a8_p682f0_w6_r13_pP.
Module C_XA_236d8_b5974_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_b5974_blk_w7_r14_L0.
Module C_XA_236d8_b5974_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_b5974_p682f0_w6_r13_pP.
Module C_XA_236d8_b649e_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_b649e_blk_w7_r14_L0.
Module C_XA_236d8_b649e_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_b649e_p682f0_w6_r13_pP.
Module C_XA_236d8_c7850_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_c7850_blk_w7_r14_L0.
Module C_XA_236d8_c7850_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_c7850_p682f0_w6_r13_pP.
Module C_XA_52944_73b21_blk_w6_r13_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_73b21_blk_w6_r13_L0.
Module C_XA_52944_73b21_p682f0_w5_r12_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_73b21_p682f0_w5_r12_pP.
Module C_ZLOOP_w4_r11_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_ZLOOP_w4_r11_pv_L0.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2.

Module LibRunUbs_u_3.
Lemma LN_TUE_T_UW_236d8_175a8_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_175a8_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_175a8_w6_r13_pP_L0.CTX C_UW_236d8_175a8_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_175a8_w6_r13_pP_L0) C_UW_236d8_175a8_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_175a8_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_175a8_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_175a8_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_175a8_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_175a8_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_175a8_p682f0_w6_r13_pP.CTX C_XA_236d8_175a8_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_175a8_p682f0_w6_r13_pP) C_XA_236d8_175a8_p682f0_w6_r13_pP.OBLS [(340%uint63, T_Ubs2UE.T_UW_236d8_175a8_w6_r13_pP_L0)] C_XA_236d8_175a8_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_175a8_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_175a8_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_175a8_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430) C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.OBLS [(168%uint63, T_Ubs2UE.T_XA_236d8_175a8_blk_w7_r14_L0); (169%uint63, T_Ubs2UE.T_XA_236d8_175a8_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f14f430.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_175a8_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_175a8_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.OBLS [(303%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f14f430 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_b5974_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_b5974_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_b5974_w7_r14_pv_L0.CTX C_UW_236d8_b5974_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_b5974_w7_r14_pv_L0) C_UW_236d8_b5974_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_b5974_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_b5974_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_b5974_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_b5974_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_b5974_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_b5974_blk_w7_r14_L0.CTX C_XA_236d8_b5974_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_b5974_blk_w7_r14_L0) C_XA_236d8_b5974_blk_w7_r14_L0.OBLS [(355%uint63, T_Ubs2UE.T_UW_236d8_b5974_w7_r14_pv_L0)] C_XA_236d8_b5974_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_b5974_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_b5974_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_b5974_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_b5974_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_b5974_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_b5974_w6_r13_pP_L0.CTX C_UW_236d8_b5974_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_b5974_w6_r13_pP_L0) C_UW_236d8_b5974_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_b5974_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_b5974_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_b5974_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_b5974_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_b5974_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_b5974_p682f0_w6_r13_pP.CTX C_XA_236d8_b5974_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_b5974_p682f0_w6_r13_pP) C_XA_236d8_b5974_p682f0_w6_r13_pP.OBLS [(354%uint63, T_Ubs2UE.T_UW_236d8_b5974_w6_r13_pP_L0)] C_XA_236d8_b5974_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_b5974_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_b5974_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_b5974_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5) C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.OBLS [(182%uint63, T_Ubs2UE.T_XA_236d8_b5974_blk_w7_r14_L0); (183%uint63, T_Ubs2UE.T_XA_236d8_b5974_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_b5974_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_b5974_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.OBLS [(304%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f9a9bb5 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_c7850_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_c7850_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_c7850_w7_r14_pv_L0.CTX C_UW_236d8_c7850_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_c7850_w7_r14_pv_L0) C_UW_236d8_c7850_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_c7850_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_c7850_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_c7850_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_c7850_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_c7850_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_c7850_blk_w7_r14_L0.CTX C_XA_236d8_c7850_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_c7850_blk_w7_r14_L0) C_XA_236d8_c7850_blk_w7_r14_L0.OBLS [(359%uint63, T_Ubs2UE.T_UW_236d8_c7850_w7_r14_pv_L0)] C_XA_236d8_c7850_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_c7850_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_c7850_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_c7850_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_c7850_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_c7850_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_c7850_w6_r13_pP_L0.CTX C_UW_236d8_c7850_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_c7850_w6_r13_pP_L0) C_UW_236d8_c7850_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_c7850_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_c7850_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_c7850_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_c7850_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_c7850_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_c7850_p682f0_w6_r13_pP.CTX C_XA_236d8_c7850_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_c7850_p682f0_w6_r13_pP) C_XA_236d8_c7850_p682f0_w6_r13_pP.OBLS [(358%uint63, T_Ubs2UE.T_UW_236d8_c7850_w6_r13_pP_L0)] C_XA_236d8_c7850_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_c7850_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_c7850_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_c7850_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd) C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.OBLS [(186%uint63, T_Ubs2UE.T_XA_236d8_c7850_blk_w7_r14_L0); (187%uint63, T_Ubs2UE.T_XA_236d8_c7850_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_fbb59fd.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_c7850_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_c7850_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.OBLS [(306%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fbb59fd _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_b649e_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_b649e_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_b649e_w7_r14_pv_L0.CTX C_UW_236d8_b649e_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_b649e_w7_r14_pv_L0) C_UW_236d8_b649e_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_b649e_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_b649e_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_b649e_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_b649e_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_b649e_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_b649e_blk_w7_r14_L0.CTX C_XA_236d8_b649e_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_b649e_blk_w7_r14_L0) C_XA_236d8_b649e_blk_w7_r14_L0.OBLS [(357%uint63, T_Ubs2UE.T_UW_236d8_b649e_w7_r14_pv_L0)] C_XA_236d8_b649e_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_b649e_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_b649e_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_b649e_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_b649e_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_b649e_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_b649e_w6_r13_pP_L0.CTX C_UW_236d8_b649e_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_b649e_w6_r13_pP_L0) C_UW_236d8_b649e_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_b649e_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_b649e_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_b649e_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_b649e_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_b649e_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_b649e_p682f0_w6_r13_pP.CTX C_XA_236d8_b649e_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_b649e_p682f0_w6_r13_pP) C_XA_236d8_b649e_p682f0_w6_r13_pP.OBLS [(356%uint63, T_Ubs2UE.T_UW_236d8_b649e_w6_r13_pP_L0)] C_XA_236d8_b649e_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_b649e_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_b649e_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_b649e_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85) C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.OBLS [(184%uint63, T_Ubs2UE.T_XA_236d8_b649e_blk_w7_r14_L0); (185%uint63, T_Ubs2UE.T_XA_236d8_b649e_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f907e85.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_b649e_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_b649e_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.OBLS [(307%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f907e85 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_15ebf_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_15ebf_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_15ebf_w7_r14_pv_L0.CTX C_UW_236d8_15ebf_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_15ebf_w7_r14_pv_L0) C_UW_236d8_15ebf_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_15ebf_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_15ebf_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_15ebf_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_15ebf_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_15ebf_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_15ebf_blk_w7_r14_L0.CTX C_XA_236d8_15ebf_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_15ebf_blk_w7_r14_L0) C_XA_236d8_15ebf_blk_w7_r14_L0.OBLS [(339%uint63, T_Ubs2UE.T_UW_236d8_15ebf_w7_r14_pv_L0)] C_XA_236d8_15ebf_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_15ebf_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_15ebf_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_15ebf_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_15ebf_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_15ebf_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_15ebf_w6_r13_pP_L0.CTX C_UW_236d8_15ebf_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_15ebf_w6_r13_pP_L0) C_UW_236d8_15ebf_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_15ebf_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_15ebf_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_15ebf_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_15ebf_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_15ebf_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_15ebf_p682f0_w6_r13_pP.CTX C_XA_236d8_15ebf_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_15ebf_p682f0_w6_r13_pP) C_XA_236d8_15ebf_p682f0_w6_r13_pP.OBLS [(338%uint63, T_Ubs2UE.T_UW_236d8_15ebf_w6_r13_pP_L0)] C_XA_236d8_15ebf_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_15ebf_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_15ebf_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_15ebf_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75) C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.OBLS [(166%uint63, T_Ubs2UE.T_XA_236d8_15ebf_blk_w7_r14_L0); (167%uint63, T_Ubs2UE.T_XA_236d8_15ebf_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f73af75.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_15ebf_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_15ebf_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.OBLS [(311%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f73af75 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.

Definition FAM_3 : list fmem := [
  FM 137%uint63 T_Ubs2U.T_ZLOOP_w4_r11_pv_L0 C_ZLOOP_w4_r11_pv_L0.CTX C_ZLOOP_w4_r11_pv_L0.PLAN C_ZLOOP_w4_r11_pv_L0.OBLS [(101%uint63, T_Ubs2U.T_FINAL_r9); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)]
  ].
Lemma FAMOK_3 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : Forall (fmem_ok SEGS R N E0 K (heads FAM_3)) FAM_3.
Proof.
  unfold FAM_3.
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w4_r11_pv_L0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w4_r11_pv_L0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w4_r11_pv_L0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_nil.
Qed.
Lemma LN_TU_T_ZLOOP_w4_r11_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_ZLOOP_w4_r11_pv_L0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_3 0 137%uint63 T_Ubs2U.T_ZLOOP_w4_r11_pv_L0 C_ZLOOP_w4_r11_pv_L0.CTX C_ZLOOP_w4_r11_pv_L0.PLAN C_ZLOOP_w4_r11_pv_L0.OBLS [(101%uint63, T_Ubs2U.T_FINAL_r9); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] (FAMOK_3 R E0 K H) eq_refl). Qed.

Definition FAM_1 : list fmem := [
  FM 204%uint63 T_Ubs2U.T_PKHEAD_m0k0 C_PKHEAD_m0k0.CTX C_PKHEAD_m0k0.PLAN C_PKHEAD_m0k0.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (206%uint63, T_Ubs2U.T_PKPOP_n_m0k0); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)];
  FM 267%uint63 T_Ubs2U.T_PKHEAD_m1k0 C_PKHEAD_m1k0.CTX C_PKHEAD_m1k0.PLAN C_PKHEAD_m1k0.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (288%uint63, T_Ubs2U.T_PKPOP_n_m1k0); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)];
  FM 205%uint63 T_Ubs2U.T_PKHEAD_m1k1 C_PKHEAD_m1k1.CTX C_PKHEAD_m1k1.PLAN C_PKHEAD_m1k1.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (266%uint63, T_Ubs2U.T_PKPOP_n_m1k1); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)];
  FM 208%uint63 T_Ubs2U.T_PKPOP_e_m0k0 C_PKPOP_e_m0k0.CTX C_PKPOP_e_m0k0.PLAN C_PKPOP_e_m0k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)];
  FM 268%uint63 T_Ubs2U.T_PKPOP_e_m1k0 C_PKPOP_e_m1k0.CTX C_PKPOP_e_m1k0.PLAN C_PKPOP_e_m1k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)];
  FM 209%uint63 T_Ubs2U.T_PKPOP_e_m1k1 C_PKPOP_e_m1k1.CTX C_PKPOP_e_m1k1.PLAN C_PKPOP_e_m1k1.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)];
  FM 206%uint63 T_Ubs2U.T_PKPOP_n_m0k0 C_PKPOP_n_m0k0.CTX C_PKPOP_n_m0k0.PLAN C_PKPOP_n_m0k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0)];
  FM 131%uint63 T_Ubs2U.T_PKPOP_n_m0k0z C_PKPOP_n_m0k0z.CTX C_PKPOP_n_m0k0z.PLAN C_PKPOP_n_m0k0z.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0)];
  FM 288%uint63 T_Ubs2U.T_PKPOP_n_m1k0 C_PKPOP_n_m1k0.CTX C_PKPOP_n_m1k0.PLAN C_PKPOP_n_m1k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)];
  FM 266%uint63 T_Ubs2U.T_PKPOP_n_m1k1 C_PKPOP_n_m1k1.CTX C_PKPOP_n_m1k1.PLAN C_PKPOP_n_m1k1.OBLS [(267%uint63, T_Ubs2U.T_PKHEAD_m1k0)];
  FM 132%uint63 T_Ubs2U.T_PKPOP_n_m1k1z C_PKPOP_n_m1k1z.CTX C_PKPOP_n_m1k1z.PLAN C_PKPOP_n_m1k1z.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (209%uint63, T_Ubs2U.T_PKPOP_e_m1k1); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0)]
  ].
Lemma FAMOK_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : Forall (fmem_ok SEGS R N E0 K (heads FAM_1)) FAM_1.
Proof.
  unfold FAM_1.
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKHEAD_m0k0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKHEAD_m0k0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKHEAD_m0k0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75 _ _ _ H)|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKHEAD_m1k0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKHEAD_m1k0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKHEAD_m1k0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75 _ _ _ H)|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKHEAD_m1k1.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKHEAD_m1k1.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKHEAD_m1k1.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85 _ _ _ H)|]; apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75 _ _ _ H)|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_e_m0k0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_e_m0k0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_e_m0k0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_e_m1k0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_e_m1k0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_e_m1k0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_e_m1k1.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_e_m1k1.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_e_m1k1.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_n_m0k0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_n_m0k0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_n_m0k0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_n_m0k0z.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_n_m0k0z.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_n_m0k0z.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_n_m1k0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_n_m1k0.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_n_m1k0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_n_m1k1.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_n_m1k1.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_n_m1k1.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_PKPOP_n_m1k1z.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_PKPOP_n_m1k1z.CTX (@h_ctabU _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_PKPOP_n_m1k1z.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_nil.
Qed.
Lemma LN_TU_T_PKHEAD_m0k0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKHEAD_m0k0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 0 204%uint63 T_Ubs2U.T_PKHEAD_m0k0 C_PKHEAD_m0k0.CTX C_PKHEAD_m0k0.PLAN C_PKHEAD_m0k0.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (206%uint63, T_Ubs2U.T_PKPOP_n_m0k0); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKHEAD_m1k0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKHEAD_m1k0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 1 267%uint63 T_Ubs2U.T_PKHEAD_m1k0 C_PKHEAD_m1k0.CTX C_PKHEAD_m1k0.PLAN C_PKHEAD_m1k0.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (288%uint63, T_Ubs2U.T_PKPOP_n_m1k0); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKHEAD_m1k1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKHEAD_m1k1).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 2 205%uint63 T_Ubs2U.T_PKHEAD_m1k1 C_PKHEAD_m1k1.CTX C_PKHEAD_m1k1.PLAN C_PKHEAD_m1k1.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (207%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e); (266%uint63, T_Ubs2U.T_PKPOP_n_m1k1); (289%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6); (290%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66); (291%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f2dbbe6); (292%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f8199b2); (293%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcd577e); (294%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fd804b6); (295%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f87081d); (296%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f341c20); (297%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f853637); (312%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f14f430); (313%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f9a9bb5); (314%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fbb59fd); (315%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f907e85); (316%uint63, T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f73af75)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_e_m0k0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_e_m0k0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 3 208%uint63 T_Ubs2U.T_PKPOP_e_m0k0 C_PKPOP_e_m0k0.CTX C_PKPOP_e_m0k0.PLAN C_PKPOP_e_m0k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_e_m1k0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_e_m1k0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 4 268%uint63 T_Ubs2U.T_PKPOP_e_m1k0 C_PKPOP_e_m1k0.CTX C_PKPOP_e_m1k0.PLAN C_PKPOP_e_m1k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_e_m1k1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_e_m1k1).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 5 209%uint63 T_Ubs2U.T_PKPOP_e_m1k1 C_PKPOP_e_m1k1.CTX C_PKPOP_e_m1k1.PLAN C_PKPOP_e_m1k1.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_n_m0k0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_n_m0k0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 6 206%uint63 T_Ubs2U.T_PKPOP_n_m0k0 C_PKPOP_n_m0k0.CTX C_PKPOP_n_m0k0.PLAN C_PKPOP_n_m0k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_n_m0k0z (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_n_m0k0z).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 7 131%uint63 T_Ubs2U.T_PKPOP_n_m0k0z C_PKPOP_n_m0k0z.CTX C_PKPOP_n_m0k0z.PLAN C_PKPOP_n_m0k0z.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (208%uint63, T_Ubs2U.T_PKPOP_e_m0k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_n_m1k0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_n_m1k0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 8 288%uint63 T_Ubs2U.T_PKPOP_n_m1k0 C_PKPOP_n_m1k0.CTX C_PKPOP_n_m1k0.PLAN C_PKPOP_n_m1k0.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1); (268%uint63, T_Ubs2U.T_PKPOP_e_m1k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_n_m1k1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_n_m1k1).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 9 266%uint63 T_Ubs2U.T_PKPOP_n_m1k1 C_PKPOP_n_m1k1.CTX C_PKPOP_n_m1k1.PLAN C_PKPOP_n_m1k1.OBLS [(267%uint63, T_Ubs2U.T_PKHEAD_m1k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TU_T_PKPOP_n_m1k1z (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PKPOP_n_m1k1z).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_1 10 132%uint63 T_Ubs2U.T_PKPOP_n_m1k1z C_PKPOP_n_m1k1z.CTX C_PKPOP_n_m1k1z.PLAN C_PKPOP_n_m1k1z.OBLS [(137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0); (209%uint63, T_Ubs2U.T_PKPOP_e_m1k1); (267%uint63, T_Ubs2U.T_PKHEAD_m1k0)] (FAMOK_1 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_UW_1f934_b775a_w5_r12_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_1f934_b775a_w5_r12_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_1f934_b775a_w5_r12_pv_L0.CTX C_UW_1f934_b775a_w5_r12_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_1f934_b775a_w5_r12_pv_L0) C_UW_1f934_b775a_w5_r12_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_1f934_b775a_w5_r12_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f934_b775a_w5_r12_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_1f934_b775a_w5_r12_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_1f934_b775a_blk_w5_r12_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_1f934_b775a_blk_w5_r12_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_1f934_b775a_blk_w5_r12_L0.CTX C_XA_1f934_b775a_blk_w5_r12_L0.PLAN (t_st T_Ubs2UE.T_XA_1f934_b775a_blk_w5_r12_L0) C_XA_1f934_b775a_blk_w5_r12_L0.OBLS [(275%uint63, T_Ubs2UE.T_UW_1f934_b775a_w5_r12_pv_L0)] C_XA_1f934_b775a_blk_w5_r12_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f934_b775a_blk_w5_r12_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_1f934_b775a_blk_w5_r12_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_1f934_b775a_w5_r12_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_1f934_b775a_w4_r11_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_1f934_b775a_w4_r11_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_1f934_b775a_w4_r11_pP_L0.CTX C_UW_1f934_b775a_w4_r11_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_1f934_b775a_w4_r11_pP_L0) C_UW_1f934_b775a_w4_r11_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_1f934_b775a_w4_r11_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f934_b775a_w4_r11_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_1f934_b775a_w4_r11_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_1f934_b775a_p682f0_w4_r11_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_1f934_b775a_p682f0_w4_r11_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_1f934_b775a_p682f0_w4_r11_pP.CTX C_XA_1f934_b775a_p682f0_w4_r11_pP.PLAN (t_st T_Ubs2UE.T_XA_1f934_b775a_p682f0_w4_r11_pP) C_XA_1f934_b775a_p682f0_w4_r11_pP.OBLS [(274%uint63, T_Ubs2UE.T_UW_1f934_b775a_w4_r11_pP_L0)] C_XA_1f934_b775a_p682f0_w4_r11_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f934_b775a_p682f0_w4_r11_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_1f934_b775a_p682f0_w4_r11_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_1f934_b775a_w4_r11_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.CTX C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.PLAN (t_st T_Ubs2U.T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6) C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.OBLS [(102%uint63, T_Ubs2UE.T_XA_1f934_b775a_blk_w5_r12_L0); (103%uint63, T_Ubs2UE.T_XA_1f934_b775a_p682f0_w4_r11_pP)] C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.WF ITAB_ok (contracts_ok_of SEGS R C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.CTX (@h_ctabUE _ _ _ H)) C_EH_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_1f934_b775a_blk_w5_r12_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_1f934_b775a_p682f0_w4_r11_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.CTX C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.PLAN (t_st T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6) C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.OBLS [(138%uint63, T_Ubs2U.T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6)] C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_1f934_s8_m5_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_73b21_w6_r13_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_73b21_w6_r13_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_73b21_w6_r13_pv_L0.CTX C_UW_52944_73b21_w6_r13_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_73b21_w6_r13_pv_L0) C_UW_52944_73b21_w6_r13_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_52944_73b21_w6_r13_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_73b21_w6_r13_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_73b21_w6_r13_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_73b21_blk_w6_r13_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_73b21_blk_w6_r13_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_73b21_blk_w6_r13_L0.CTX C_XA_52944_73b21_blk_w6_r13_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_73b21_blk_w6_r13_L0) C_XA_52944_73b21_blk_w6_r13_L0.OBLS [(383%uint63, T_Ubs2UE.T_UW_52944_73b21_w6_r13_pv_L0)] C_XA_52944_73b21_blk_w6_r13_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_73b21_blk_w6_r13_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_73b21_blk_w6_r13_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_73b21_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_73b21_w5_r12_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_73b21_w5_r12_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_73b21_w5_r12_pP_L0.CTX C_UW_52944_73b21_w5_r12_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_73b21_w5_r12_pP_L0) C_UW_52944_73b21_w5_r12_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_52944_73b21_w5_r12_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_73b21_w5_r12_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_73b21_w5_r12_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_73b21_p682f0_w5_r12_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_73b21_p682f0_w5_r12_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_73b21_p682f0_w5_r12_pP.CTX C_XA_52944_73b21_p682f0_w5_r12_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_73b21_p682f0_w5_r12_pP) C_XA_52944_73b21_p682f0_w5_r12_pP.OBLS [(382%uint63, T_Ubs2UE.T_UW_52944_73b21_w5_r12_pP_L0)] C_XA_52944_73b21_p682f0_w5_r12_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_73b21_p682f0_w5_r12_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_73b21_p682f0_w5_r12_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_73b21_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_3.
