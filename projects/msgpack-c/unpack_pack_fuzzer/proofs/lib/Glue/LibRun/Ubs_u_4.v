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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require B_00 B_01.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_03 B_04 B_05 B_09 B_13.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.LibRun Require Ubs_u_1 Ubs_u_2 Ubs_u_3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.
Module C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.
Module C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.
Module C_EXECRET_rc0_m1_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc0_m1_n12_w01113.
Module C_EXECRET_rc2_m2_t0_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t0_n12_w01113.
Module C_EXECRET_rc2_m2_t1_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t1_n12_w01113.
Module C_EXECRET_rc2_m2_t2_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t2_n12_w01113.
Module C_EXECRET_rc2_m2_t3_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t3_n12_w01113.
Module C_EXECRET_rc2_m2_t4_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t4_n12_w01113.
Module C_EXECRET_rc2_m2_t5_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t5_n12_w01113.
Module C_EXECRET_rc2_m2_t5z_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t5z_n12_w01113.
Module C_EXECRET_rc2_m2_t6_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t6_n12_w01113.
Module C_EXECRET_rc2_m2_t7z_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t7z_n12_w01113.
Module C_EXECRET_rc2_m2_t8z_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t8z_n12_w01113.
Module C_EXECRET_rc2_m2_t9_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_t9_n12_w01113.
Module C_EXECRET_rc2_m2_ta_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_ta_n12_w01113.
Module C_EXECRET_rc2_m2_tx_n12_w01113 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc2_m2_tx_n12_w01113.
Module C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.
Module C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.
Module C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.
Module C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_01.C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.
Module C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.
Module C_UW_21778_a5925_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_21778_a5925_w7_r14_pP_L0.
Module C_UW_21778_a5925_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_21778_a5925_w8_r15_pv_L0.
Module C_UW_223c4_982fd_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_982fd_w7_r14_pv_L0.
Module C_UW_223c4_da298_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_223c4_da298_w6_r13_pP_L0.
Module C_UW_223c4_da298_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_05.C_UW_223c4_da298_w7_r14_pv_L0.
Module C_UW_52944_7f9b2_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_7f9b2_w6_r13_pP_L0.
Module C_UW_52944_7f9b2_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_7f9b2_w7_r14_pP_L0.
Module C_UW_52944_8799c_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_8799c_w7_r14_pP_L0.
Module C_UW_52944_8799c_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_8799c_w8_r15_pv_L0.
Module C_XA_21778_a5925_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_21778_a5925_blk_w7_r14_L0.
Module C_XA_21778_a5925_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_21778_a5925_p682f0_w6_r13_pP.
Module C_XA_223c4_da298_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_da298_blk_w7_r14_L0.
Module C_XA_223c4_da298_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_223c4_da298_p682f0_w6_r13_pP.
Module C_XA_52944_7f9b2_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_7f9b2_blk_w7_r14_L0.
Module C_XA_52944_7f9b2_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_7f9b2_p68250_w6_r13_pP.
Module C_XA_52944_8799c_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_8799c_blk_w8_r15_L0.
Module C_XA_52944_8799c_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_8799c_p682f0_w7_r14_pP.
Import Ubs_u_1.LibRunUbs_u_1 Ubs_u_2.LibRunUbs_u_2 Ubs_u_3.LibRunUbs_u_3.

Module LibRunUbs_u_4.
Lemma LN_TU_T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.CTX C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e) C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.OBLS [(210%uint63, T_Ubs2UE.T_XA_52944_73b21_blk_w6_r13_L0); (211%uint63, T_Ubs2UE.T_XA_52944_73b21_p682f0_w5_r12_pP)] C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w5_r12_pv_L0_f2b130e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_73b21_blk_w6_r13_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_73b21_p682f0_w5_r12_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.CTX C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.PLAN (t_st T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e) C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.OBLS [(149%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e)] C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w5_r12_pv_L0_f2b130e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_tx_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_tx_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_tx_n12_w01113.CTX C_EXECRET_rc2_m2_tx_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_tx_n12_w01113) C_EXECRET_rc2_m2_tx_n12_w01113.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (134%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e); (204%uint63, T_Ubs2U.T_PKHEAD_m0k0); (205%uint63, T_Ubs2U.T_PKHEAD_m1k1)] C_EXECRET_rc2_m2_tx_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_tx_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_tx_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PKPOP_n_m0k0z _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PKPOP_n_m1k1z _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PKHEAD_m0k0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PKHEAD_m1k1 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.CTX C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.PLAN (t_st T_Ubs2U.T_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22) C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.OBLS [(139%uint63, T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22)] C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc0_m1_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc0_m1_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc0_m1_n12_w01113.CTX C_EXECRET_rc0_m1_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc0_m1_n12_w01113) C_EXECRET_rc0_m1_n12_w01113.OBLS [(135%uint63, T_Ubs2U.T_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22)] C_EXECRET_rc0_m1_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc0_m1_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc0_m1_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROW_2037c_s10_m1_w5_r12_pv_L0_fcc6b22 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t0_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t0_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t0_n12_w01113.CTX C_EXECRET_rc2_m2_t0_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t0_n12_w01113) C_EXECRET_rc2_m2_t0_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t0_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t0_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t0_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t1_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t1_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t1_n12_w01113.CTX C_EXECRET_rc2_m2_t1_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t1_n12_w01113) C_EXECRET_rc2_m2_t1_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t1_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t1_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t1_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t2_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t2_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t2_n12_w01113.CTX C_EXECRET_rc2_m2_t2_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t2_n12_w01113) C_EXECRET_rc2_m2_t2_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t2_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t2_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t2_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t3_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t3_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t3_n12_w01113.CTX C_EXECRET_rc2_m2_t3_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t3_n12_w01113) C_EXECRET_rc2_m2_t3_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t3_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t3_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t3_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t4_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t4_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t4_n12_w01113.CTX C_EXECRET_rc2_m2_t4_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t4_n12_w01113) C_EXECRET_rc2_m2_t4_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t4_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t4_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t4_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t5_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t5_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t5_n12_w01113.CTX C_EXECRET_rc2_m2_t5_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t5_n12_w01113) C_EXECRET_rc2_m2_t5_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t5_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t5_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t5_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t5z_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t5z_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t5z_n12_w01113.CTX C_EXECRET_rc2_m2_t5z_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t5z_n12_w01113) C_EXECRET_rc2_m2_t5z_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t5z_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t5z_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t5z_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t6_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t6_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t6_n12_w01113.CTX C_EXECRET_rc2_m2_t6_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t6_n12_w01113) C_EXECRET_rc2_m2_t6_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t6_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t6_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t6_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t7z_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t7z_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t7z_n12_w01113.CTX C_EXECRET_rc2_m2_t7z_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t7z_n12_w01113) C_EXECRET_rc2_m2_t7z_n12_w01113.OBLS [(131%uint63, T_Ubs2U.T_PKPOP_n_m0k0z); (133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (134%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e)] C_EXECRET_rc2_m2_t7z_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t7z_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t7z_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PKPOP_n_m0k0z _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t8z_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t8z_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t8z_n12_w01113.CTX C_EXECRET_rc2_m2_t8z_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t8z_n12_w01113) C_EXECRET_rc2_m2_t8z_n12_w01113.OBLS [(132%uint63, T_Ubs2U.T_PKPOP_n_m1k1z); (133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (134%uint63, T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e)] C_EXECRET_rc2_m2_t8z_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t8z_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t8z_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PKPOP_n_m1k1z _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_52944_s8_m3_w5_r12_pv_L0_f2b130e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_t9_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_t9_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_t9_n12_w01113.CTX C_EXECRET_rc2_m2_t9_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_t9_n12_w01113) C_EXECRET_rc2_m2_t9_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_t9_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_t9_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_t9_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc2_m2_ta_n12_w01113 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc2_m2_ta_n12_w01113).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc2_m2_ta_n12_w01113.CTX C_EXECRET_rc2_m2_ta_n12_w01113.PLAN (t_st T_Ubs2U.T_EXECRET_rc2_m2_ta_n12_w01113) C_EXECRET_rc2_m2_ta_n12_w01113.OBLS [(133%uint63, T_Ubs2U.T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6); (137%uint63, T_Ubs2U.T_ZLOOP_w4_r11_pv_L0)] C_EXECRET_rc2_m2_ta_n12_w01113.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc2_m2_ta_n12_w01113.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc2_m2_ta_n12_w01113.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROWPK_1f934_s8_m3_w4_r11_pv_L0_f4e7bc6 _ _ _ H)|]; apply Forall_cons; [exact (LN_TU_T_ZLOOP_w4_r11_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_8799c_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_8799c_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_8799c_w8_r15_pv_L0.CTX C_UW_52944_8799c_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_8799c_w8_r15_pv_L0) C_UW_52944_8799c_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_8799c_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_8799c_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_8799c_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_8799c_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_8799c_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_8799c_blk_w8_r15_L0.CTX C_XA_52944_8799c_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_8799c_blk_w8_r15_L0) C_XA_52944_8799c_blk_w8_r15_L0.OBLS [(539%uint63, T_Ubs2UE.T_UW_52944_8799c_w8_r15_pv_L0)] C_XA_52944_8799c_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_8799c_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_8799c_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_8799c_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_8799c_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_8799c_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_8799c_w7_r14_pP_L0.CTX C_UW_52944_8799c_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_8799c_w7_r14_pP_L0) C_UW_52944_8799c_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_8799c_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_8799c_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_8799c_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_8799c_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_8799c_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_8799c_p682f0_w7_r14_pP.CTX C_XA_52944_8799c_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_8799c_p682f0_w7_r14_pP) C_XA_52944_8799c_p682f0_w7_r14_pP.OBLS [(538%uint63, T_Ubs2UE.T_UW_52944_8799c_w7_r14_pP_L0)] C_XA_52944_8799c_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_8799c_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_8799c_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_8799c_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1) C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.OBLS [(454%uint63, T_Ubs2UE.T_XA_52944_8799c_blk_w8_r15_L0); (455%uint63, T_Ubs2UE.T_XA_52944_8799c_p682f0_w7_r14_pP)] C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_8799c_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_8799c_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_21778_a5925_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_21778_a5925_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_21778_a5925_w8_r15_pv_L0.CTX C_UW_21778_a5925_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_21778_a5925_w8_r15_pv_L0) C_UW_21778_a5925_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_21778_a5925_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_21778_a5925_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_21778_a5925_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_21778_a5925_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_21778_a5925_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_21778_a5925_blk_w7_r14_L0.CTX C_XA_21778_a5925_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_21778_a5925_blk_w7_r14_L0) C_XA_21778_a5925_blk_w7_r14_L0.OBLS [(236%uint63, T_Ubs2UE.T_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1); (281%uint63, T_Ubs2UE.T_UW_21778_a5925_w8_r15_pv_L0)] C_XA_21778_a5925_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_21778_a5925_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_21778_a5925_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_21778_a5925_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_21778_a5925_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_7f9b2_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_7f9b2_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_7f9b2_w7_r14_pP_L0.CTX C_UW_52944_7f9b2_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_7f9b2_w7_r14_pP_L0) C_UW_52944_7f9b2_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_7f9b2_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_7f9b2_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_7f9b2_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_7f9b2_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_7f9b2_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_7f9b2_blk_w7_r14_L0.CTX C_XA_52944_7f9b2_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_7f9b2_blk_w7_r14_L0) C_XA_52944_7f9b2_blk_w7_r14_L0.OBLS [(533%uint63, T_Ubs2UE.T_UW_52944_7f9b2_w7_r14_pP_L0)] C_XA_52944_7f9b2_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_7f9b2_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_7f9b2_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_7f9b2_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_7f9b2_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_7f9b2_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_7f9b2_w6_r13_pP_L0.CTX C_UW_52944_7f9b2_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_7f9b2_w6_r13_pP_L0) C_UW_52944_7f9b2_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_7f9b2_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_7f9b2_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_7f9b2_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_7f9b2_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_7f9b2_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_7f9b2_p68250_w6_r13_pP.CTX C_XA_52944_7f9b2_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_7f9b2_p68250_w6_r13_pP) C_XA_52944_7f9b2_p68250_w6_r13_pP.OBLS [(532%uint63, T_Ubs2UE.T_UW_52944_7f9b2_w6_r13_pP_L0)] C_XA_52944_7f9b2_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_7f9b2_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_7f9b2_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_7f9b2_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.OBLS [(448%uint63, T_Ubs2UE.T_XA_52944_7f9b2_blk_w7_r14_L0); (449%uint63, T_Ubs2UE.T_XA_52944_7f9b2_p68250_w6_r13_pP)] C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_7f9b2_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_7f9b2_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_21778_a5925_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_21778_a5925_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_21778_a5925_w7_r14_pP_L0.CTX C_UW_21778_a5925_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_21778_a5925_w7_r14_pP_L0) C_UW_21778_a5925_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_21778_a5925_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_21778_a5925_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_21778_a5925_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_21778_a5925_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_21778_a5925_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_21778_a5925_p682f0_w6_r13_pP.CTX C_XA_21778_a5925_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_21778_a5925_p682f0_w6_r13_pP) C_XA_21778_a5925_p682f0_w6_r13_pP.OBLS [(237%uint63, T_Ubs2UE.T_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1); (280%uint63, T_Ubs2UE.T_UW_21778_a5925_w7_r14_pP_L0)] C_XA_21778_a5925_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_21778_a5925_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_21778_a5925_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_21778_a5925_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_21778_a5925_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.CTX C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.PLAN (t_st T_Ubs2U.T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33) C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.OBLS [(108%uint63, T_Ubs2UE.T_XA_21778_a5925_blk_w7_r14_L0); (109%uint63, T_Ubs2UE.T_XA_21778_a5925_p682f0_w6_r13_pP)] C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.WF ITAB_ok (contracts_ok_of SEGS R C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.CTX (@h_ctabUE _ _ _ H)) C_EH_21778_s10_m5_w6_r13_pv_L0_feddc33.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_21778_a5925_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_21778_a5925_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.CTX C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.PLAN (t_st T_Ubs2U.T_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33) C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.OBLS [(140%uint63, T_Ubs2U.T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33)] C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_21778_s10_m1_w5_r12_pv_L0_feddc33.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_21778_s10_m5_w6_r13_pv_L0_feddc33 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_da298_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_da298_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_da298_w7_r14_pv_L0.CTX C_UW_223c4_da298_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_da298_w7_r14_pv_L0) C_UW_223c4_da298_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_223c4_da298_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_da298_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_da298_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_da298_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_da298_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_da298_blk_w7_r14_L0.CTX C_XA_223c4_da298_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_223c4_da298_blk_w7_r14_L0) C_XA_223c4_da298_blk_w7_r14_L0.OBLS [(303%uint63, T_Ubs2UE.T_UW_223c4_da298_w7_r14_pv_L0)] C_XA_223c4_da298_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_da298_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_da298_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_da298_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_da298_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_da298_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_da298_w6_r13_pP_L0.CTX C_UW_223c4_da298_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_da298_w6_r13_pP_L0) C_UW_223c4_da298_w6_r13_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_223c4_da298_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_da298_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_da298_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_223c4_da298_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_223c4_da298_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_223c4_da298_p682f0_w6_r13_pP.CTX C_XA_223c4_da298_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_223c4_da298_p682f0_w6_r13_pP) C_XA_223c4_da298_p682f0_w6_r13_pP.OBLS [(302%uint63, T_Ubs2UE.T_UW_223c4_da298_w6_r13_pP_L0)] C_XA_223c4_da298_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_223c4_da298_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_223c4_da298_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_223c4_da298_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.CTX C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.PLAN (t_st T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0) C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.OBLS [(130%uint63, T_Ubs2UE.T_XA_223c4_da298_blk_w7_r14_L0); (131%uint63, T_Ubs2UE.T_XA_223c4_da298_p682f0_w6_r13_pP)] C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.WF ITAB_ok (contracts_ok_of SEGS R C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.CTX (@h_ctabUE _ _ _ H)) C_EH_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_223c4_da298_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_223c4_da298_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.CTX C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.PLAN (t_st T_Ubs2U.T_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.OBLS [(141%uint63, T_Ubs2U.T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0)] C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_223c4_s8_m1_w5_r12_pv_L0_f8ed8f0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_223c4_s8_m5_w6_r13_pv_L0_f8ed8f0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_223c4_982fd_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_223c4_982fd_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_223c4_982fd_w7_r14_pv_L0.CTX C_UW_223c4_982fd_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_223c4_982fd_w7_r14_pv_L0) C_UW_223c4_982fd_w7_r14_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_223c4_982fd_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_223c4_982fd_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_223c4_982fd_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_4.
