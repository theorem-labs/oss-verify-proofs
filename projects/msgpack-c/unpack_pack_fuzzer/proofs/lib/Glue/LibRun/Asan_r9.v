(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgAsan ItabAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require T_Asan2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L Require T_Asan2L B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E Require T_Asan2E B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib.
Open Scope Z_scope.
Unset Lia Cache.
Module DF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F.T_Asan2F.
Module TL := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L.T_Asan2L.
Module TE := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.T_Asan2E.
Module C_EH_8d6b8_LIBENT_r9_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_EH_8d6b8_LIBENT_r9_1.
Module C_EH_8d78c_LIBENT_r9_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_EH_8d78c_LIBENT_r9_2.
Module C_EH_8e7a8_LIBENT_r9_4 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_EH_8e7a8_LIBENT_r9_4.
Module C_EH_ccc04_LIBENT_r9_3 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_EH_ccc04_LIBENT_r9_3.
Module C_THROW2_ccc04_pP_q499a := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_THROW2_ccc04_pP_q499a.
Module C_THROW2_ccc04_pv_q3057 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_THROW2_ccc04_pv_q3057.
Module C_UW_8d6b8_ce6cb_w10_r20_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_8d6b8_ce6cb_w10_r20_pv_L0.
Module C_UW_8d6b8_ce6cb_w8_r18_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_8d6b8_ce6cb_w8_r18_pP_L0.
Module C_UW_8d78c_5d773_w10_r20_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_8d78c_5d773_w10_r20_pP_L0.
Module C_UW_8d78c_5d773_w12_r22_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_8d78c_5d773_w12_r22_pv_L0.
Module C_UW_8e7a8_1adca_w18_r28_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_8e7a8_1adca_w18_r28_pP_L0.
Module C_UW_8e7a8_1adca_w20_r30_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_8e7a8_1adca_w20_r30_pv_L0.
Module C_UW_ccc04_f041d_w12_r22_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_ccc04_f041d_w12_r22_pP_L0.
Module C_UW_ccc04_f041d_w14_r24_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_ccc04_f041d_w14_r24_pv_L0.
Module C_UW_r_bba23_w18_r28_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_r_bba23_w18_r28_pP_L0.
Module C_UW_r_bba23_w20_r30_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_r_bba23_w20_r30_pv_L0.
Module C_UW_r_ff863_w16_r26_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_r_ff863_w16_r26_pP_L0.
Module C_UW_r_ff863_w18_r28_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_UW_r_ff863_w18_r28_pP_L0.
Module C_XA_8d6b8_ce6cb_blk_w10_r20_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_8d6b8_ce6cb_blk_w10_r20_L0.
Module C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.
Module C_XA_8d78c_5d773_blk_w12_r22_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_8d78c_5d773_blk_w12_r22_L0.
Module C_XA_8d78c_5d773_p60c2a0_w10_r20_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.
Module C_XA_8e7a8_1adca_blk_w18_r28_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_8e7a8_1adca_blk_w18_r28_L0.
Module C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.
Module C_XA_ccc04_f041d_blk_w14_r24_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_ccc04_f041d_blk_w14_r24_L0.
Module C_XA_ccc04_f041d_p60c2a0_w12_r22_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.
Module C_XA_r_bba23_blk_w20_r30_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_r_bba23_blk_w20_r30_L0.
Module C_XA_r_bba23_p60c2a0_w18_r28_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_r_bba23_p60c2a0_w18_r28_pP.
Module C_XA_r_ff863_blk_w18_r28_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_r_ff863_blk_w18_r28_L0.
Module C_XA_r_ff863_p60c200_w16_r26_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2E.B_00.C_XA_r_ff863_p60c200_w16_r26_pP.
Module C_LIBENT_r9 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2L.B_00.C_LIBENT_r9.

Module LibRunAsan_r9.
Definition N : int := 185%uint63.
Section A.
Variable R : drun.
Variables (E0 : env) (K : TSet).
Record hyps : Prop := Hyps {
  h_pb : r_PB R (eb E0);
  h_ctabL : ctab_ok SEGS R TL.CONTRACTS;
  h_ctabE : ctab_ok SEGS R TE.CONTRACTS;
  h_ret : LNODE SEGS R N E0 K (t_st DF.R_LIBGEN_r9_RET) }.

Lemma LN_T_UW_8d6b8_ce6cb_w10_r20_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8d6b8_ce6cb_w10_r20_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8d6b8_ce6cb_w10_r20_pv_L0.CTX C_UW_8d6b8_ce6cb_w10_r20_pv_L0.PLAN (t_st TE.T_UW_8d6b8_ce6cb_w10_r20_pv_L0) C_UW_8d6b8_ce6cb_w10_r20_pv_L0.OBLS C_UW_8d6b8_ce6cb_w10_r20_pv_L0.CUTL C_UW_8d6b8_ce6cb_w10_r20_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8d6b8_ce6cb_w10_r20_pv_L0.CTX (h_ctabE H)) C_UW_8d6b8_ce6cb_w10_r20_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8d6b8_ce6cb_w10_r20_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8d6b8_ce6cb_blk_w10_r20_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8d6b8_ce6cb_blk_w10_r20_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8d6b8_ce6cb_blk_w10_r20_L0.CTX C_XA_8d6b8_ce6cb_blk_w10_r20_L0.PLAN (t_st TE.T_XA_8d6b8_ce6cb_blk_w10_r20_L0) C_XA_8d6b8_ce6cb_blk_w10_r20_L0.OBLS C_XA_8d6b8_ce6cb_blk_w10_r20_L0.CUTL C_XA_8d6b8_ce6cb_blk_w10_r20_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8d6b8_ce6cb_blk_w10_r20_L0.CTX (h_ctabE H)) C_XA_8d6b8_ce6cb_blk_w10_r20_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8d6b8_ce6cb_blk_w10_r20_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_8d6b8_ce6cb_w10_r20_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8d6b8_ce6cb_w8_r18_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8d6b8_ce6cb_w8_r18_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8d6b8_ce6cb_w8_r18_pP_L0.CTX C_UW_8d6b8_ce6cb_w8_r18_pP_L0.PLAN (t_st TE.T_UW_8d6b8_ce6cb_w8_r18_pP_L0) C_UW_8d6b8_ce6cb_w8_r18_pP_L0.OBLS C_UW_8d6b8_ce6cb_w8_r18_pP_L0.CUTL C_UW_8d6b8_ce6cb_w8_r18_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8d6b8_ce6cb_w8_r18_pP_L0.CTX (h_ctabE H)) C_UW_8d6b8_ce6cb_w8_r18_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8d6b8_ce6cb_w8_r18_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.CTX C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.PLAN (t_st TE.T_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP) C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.OBLS C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.CUTL C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.CTX (h_ctabE H)) C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_8d6b8_ce6cb_w8_r18_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_8d6b8_LIBENT_r9_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_8d6b8_LIBENT_r9_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_8d6b8_LIBENT_r9_1.CTX C_EH_8d6b8_LIBENT_r9_1.PLAN (t_st TL.T_THROW_8d6b8_LIBENT_r9_1) C_EH_8d6b8_LIBENT_r9_1.OBLS C_EH_8d6b8_LIBENT_r9_1.CUTL C_EH_8d6b8_LIBENT_r9_1.WF ITAB_ok (contracts_ok_of SEGS R C_EH_8d6b8_LIBENT_r9_1.CTX (h_ctabE H)) C_EH_8d6b8_LIBENT_r9_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_8d6b8_LIBENT_r9_1.CUTL]; apply Forall_cons; [exact (LN_T_XA_8d6b8_ce6cb_blk_w10_r20_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_8d6b8_ce6cb_p60c2a0_w8_r18_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8d78c_5d773_w12_r22_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8d78c_5d773_w12_r22_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8d78c_5d773_w12_r22_pv_L0.CTX C_UW_8d78c_5d773_w12_r22_pv_L0.PLAN (t_st TE.T_UW_8d78c_5d773_w12_r22_pv_L0) C_UW_8d78c_5d773_w12_r22_pv_L0.OBLS C_UW_8d78c_5d773_w12_r22_pv_L0.CUTL C_UW_8d78c_5d773_w12_r22_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8d78c_5d773_w12_r22_pv_L0.CTX (h_ctabE H)) C_UW_8d78c_5d773_w12_r22_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8d78c_5d773_w12_r22_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8d78c_5d773_blk_w12_r22_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8d78c_5d773_blk_w12_r22_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8d78c_5d773_blk_w12_r22_L0.CTX C_XA_8d78c_5d773_blk_w12_r22_L0.PLAN (t_st TE.T_XA_8d78c_5d773_blk_w12_r22_L0) C_XA_8d78c_5d773_blk_w12_r22_L0.OBLS C_XA_8d78c_5d773_blk_w12_r22_L0.CUTL C_XA_8d78c_5d773_blk_w12_r22_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8d78c_5d773_blk_w12_r22_L0.CTX (h_ctabE H)) C_XA_8d78c_5d773_blk_w12_r22_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8d78c_5d773_blk_w12_r22_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_8d78c_5d773_w12_r22_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8d78c_5d773_w10_r20_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8d78c_5d773_w10_r20_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8d78c_5d773_w10_r20_pP_L0.CTX C_UW_8d78c_5d773_w10_r20_pP_L0.PLAN (t_st TE.T_UW_8d78c_5d773_w10_r20_pP_L0) C_UW_8d78c_5d773_w10_r20_pP_L0.OBLS C_UW_8d78c_5d773_w10_r20_pP_L0.CUTL C_UW_8d78c_5d773_w10_r20_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8d78c_5d773_w10_r20_pP_L0.CTX (h_ctabE H)) C_UW_8d78c_5d773_w10_r20_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8d78c_5d773_w10_r20_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8d78c_5d773_p60c2a0_w10_r20_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8d78c_5d773_p60c2a0_w10_r20_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.CTX C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.PLAN (t_st TE.T_XA_8d78c_5d773_p60c2a0_w10_r20_pP) C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.OBLS C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.CUTL C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.CTX (h_ctabE H)) C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8d78c_5d773_p60c2a0_w10_r20_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_8d78c_5d773_w10_r20_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_8d78c_LIBENT_r9_2 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_8d78c_LIBENT_r9_2).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_8d78c_LIBENT_r9_2.CTX C_EH_8d78c_LIBENT_r9_2.PLAN (t_st TL.T_THROW_8d78c_LIBENT_r9_2) C_EH_8d78c_LIBENT_r9_2.OBLS C_EH_8d78c_LIBENT_r9_2.CUTL C_EH_8d78c_LIBENT_r9_2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_8d78c_LIBENT_r9_2.CTX (h_ctabE H)) C_EH_8d78c_LIBENT_r9_2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_8d78c_LIBENT_r9_2.CUTL]; apply Forall_cons; [exact (LN_T_XA_8d78c_5d773_blk_w12_r22_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_8d78c_5d773_p60c2a0_w10_r20_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_r_bba23_w20_r30_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_r_bba23_w20_r30_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_r_bba23_w20_r30_pv_L0.CTX C_UW_r_bba23_w20_r30_pv_L0.PLAN (t_st TE.T_UW_r_bba23_w20_r30_pv_L0) C_UW_r_bba23_w20_r30_pv_L0.OBLS C_UW_r_bba23_w20_r30_pv_L0.CUTL C_UW_r_bba23_w20_r30_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_r_bba23_w20_r30_pv_L0.CTX (h_ctabE H)) C_UW_r_bba23_w20_r30_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_r_bba23_w20_r30_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_r_bba23_blk_w20_r30_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_r_bba23_blk_w20_r30_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_r_bba23_blk_w20_r30_L0.CTX C_XA_r_bba23_blk_w20_r30_L0.PLAN (t_st TE.T_XA_r_bba23_blk_w20_r30_L0) C_XA_r_bba23_blk_w20_r30_L0.OBLS C_XA_r_bba23_blk_w20_r30_L0.CUTL C_XA_r_bba23_blk_w20_r30_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_r_bba23_blk_w20_r30_L0.CTX (h_ctabE H)) C_XA_r_bba23_blk_w20_r30_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_r_bba23_blk_w20_r30_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_r_bba23_w20_r30_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_r_bba23_w18_r28_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_r_bba23_w18_r28_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_r_bba23_w18_r28_pP_L0.CTX C_UW_r_bba23_w18_r28_pP_L0.PLAN (t_st TE.T_UW_r_bba23_w18_r28_pP_L0) C_UW_r_bba23_w18_r28_pP_L0.OBLS C_UW_r_bba23_w18_r28_pP_L0.CUTL C_UW_r_bba23_w18_r28_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_r_bba23_w18_r28_pP_L0.CTX (h_ctabE H)) C_UW_r_bba23_w18_r28_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_r_bba23_w18_r28_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_r_bba23_p60c2a0_w18_r28_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_r_bba23_p60c2a0_w18_r28_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_r_bba23_p60c2a0_w18_r28_pP.CTX C_XA_r_bba23_p60c2a0_w18_r28_pP.PLAN (t_st TE.T_XA_r_bba23_p60c2a0_w18_r28_pP) C_XA_r_bba23_p60c2a0_w18_r28_pP.OBLS C_XA_r_bba23_p60c2a0_w18_r28_pP.CUTL C_XA_r_bba23_p60c2a0_w18_r28_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_r_bba23_p60c2a0_w18_r28_pP.CTX (h_ctabE H)) C_XA_r_bba23_p60c2a0_w18_r28_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_r_bba23_p60c2a0_w18_r28_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_r_bba23_w18_r28_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW2_ccc04_pv_q3057 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_THROW2_ccc04_pv_q3057).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_THROW2_ccc04_pv_q3057.CTX C_THROW2_ccc04_pv_q3057.PLAN (t_st TE.T_THROW2_ccc04_pv_q3057) C_THROW2_ccc04_pv_q3057.OBLS C_THROW2_ccc04_pv_q3057.CUTL C_THROW2_ccc04_pv_q3057.WF ITAB_ok (contracts_ok_of SEGS R C_THROW2_ccc04_pv_q3057.CTX (h_ctabE H)) C_THROW2_ccc04_pv_q3057.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_THROW2_ccc04_pv_q3057.CUTL]; apply Forall_cons; [exact (LN_T_XA_r_bba23_blk_w20_r30_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_r_bba23_p60c2a0_w18_r28_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8e7a8_1adca_w20_r30_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8e7a8_1adca_w20_r30_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8e7a8_1adca_w20_r30_pv_L0.CTX C_UW_8e7a8_1adca_w20_r30_pv_L0.PLAN (t_st TE.T_UW_8e7a8_1adca_w20_r30_pv_L0) C_UW_8e7a8_1adca_w20_r30_pv_L0.OBLS C_UW_8e7a8_1adca_w20_r30_pv_L0.CUTL C_UW_8e7a8_1adca_w20_r30_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8e7a8_1adca_w20_r30_pv_L0.CTX (h_ctabE H)) C_UW_8e7a8_1adca_w20_r30_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8e7a8_1adca_w20_r30_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8e7a8_1adca_blk_w18_r28_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8e7a8_1adca_blk_w18_r28_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8e7a8_1adca_blk_w18_r28_L0.CTX C_XA_8e7a8_1adca_blk_w18_r28_L0.PLAN (t_st TE.T_XA_8e7a8_1adca_blk_w18_r28_L0) C_XA_8e7a8_1adca_blk_w18_r28_L0.OBLS C_XA_8e7a8_1adca_blk_w18_r28_L0.CUTL C_XA_8e7a8_1adca_blk_w18_r28_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8e7a8_1adca_blk_w18_r28_L0.CTX (h_ctabE H)) C_XA_8e7a8_1adca_blk_w18_r28_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8e7a8_1adca_blk_w18_r28_L0.CUTL]; apply Forall_cons; [exact (LN_T_THROW2_ccc04_pv_q3057 H)|]; apply Forall_cons; [exact (LN_T_UW_8e7a8_1adca_w20_r30_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_r_ff863_w18_r28_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_r_ff863_w18_r28_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_r_ff863_w18_r28_pP_L0.CTX C_UW_r_ff863_w18_r28_pP_L0.PLAN (t_st TE.T_UW_r_ff863_w18_r28_pP_L0) C_UW_r_ff863_w18_r28_pP_L0.OBLS C_UW_r_ff863_w18_r28_pP_L0.CUTL C_UW_r_ff863_w18_r28_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_r_ff863_w18_r28_pP_L0.CTX (h_ctabE H)) C_UW_r_ff863_w18_r28_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_r_ff863_w18_r28_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_r_ff863_blk_w18_r28_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_r_ff863_blk_w18_r28_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_r_ff863_blk_w18_r28_L0.CTX C_XA_r_ff863_blk_w18_r28_L0.PLAN (t_st TE.T_XA_r_ff863_blk_w18_r28_L0) C_XA_r_ff863_blk_w18_r28_L0.OBLS C_XA_r_ff863_blk_w18_r28_L0.CUTL C_XA_r_ff863_blk_w18_r28_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_r_ff863_blk_w18_r28_L0.CTX (h_ctabE H)) C_XA_r_ff863_blk_w18_r28_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_r_ff863_blk_w18_r28_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_r_ff863_w18_r28_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_r_ff863_w16_r26_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_r_ff863_w16_r26_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_r_ff863_w16_r26_pP_L0.CTX C_UW_r_ff863_w16_r26_pP_L0.PLAN (t_st TE.T_UW_r_ff863_w16_r26_pP_L0) C_UW_r_ff863_w16_r26_pP_L0.OBLS C_UW_r_ff863_w16_r26_pP_L0.CUTL C_UW_r_ff863_w16_r26_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_r_ff863_w16_r26_pP_L0.CTX (h_ctabE H)) C_UW_r_ff863_w16_r26_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_r_ff863_w16_r26_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_r_ff863_p60c200_w16_r26_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_r_ff863_p60c200_w16_r26_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_r_ff863_p60c200_w16_r26_pP.CTX C_XA_r_ff863_p60c200_w16_r26_pP.PLAN (t_st TE.T_XA_r_ff863_p60c200_w16_r26_pP) C_XA_r_ff863_p60c200_w16_r26_pP.OBLS C_XA_r_ff863_p60c200_w16_r26_pP.CUTL C_XA_r_ff863_p60c200_w16_r26_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_r_ff863_p60c200_w16_r26_pP.CTX (h_ctabE H)) C_XA_r_ff863_p60c200_w16_r26_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_r_ff863_p60c200_w16_r26_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_r_ff863_w16_r26_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW2_ccc04_pP_q499a (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_THROW2_ccc04_pP_q499a).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_THROW2_ccc04_pP_q499a.CTX C_THROW2_ccc04_pP_q499a.PLAN (t_st TE.T_THROW2_ccc04_pP_q499a) C_THROW2_ccc04_pP_q499a.OBLS C_THROW2_ccc04_pP_q499a.CUTL C_THROW2_ccc04_pP_q499a.WF ITAB_ok (contracts_ok_of SEGS R C_THROW2_ccc04_pP_q499a.CTX (h_ctabE H)) C_THROW2_ccc04_pP_q499a.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_THROW2_ccc04_pP_q499a.CUTL]; apply Forall_cons; [exact (LN_T_XA_r_ff863_blk_w18_r28_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_r_ff863_p60c200_w16_r26_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8e7a8_1adca_w18_r28_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8e7a8_1adca_w18_r28_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8e7a8_1adca_w18_r28_pP_L0.CTX C_UW_8e7a8_1adca_w18_r28_pP_L0.PLAN (t_st TE.T_UW_8e7a8_1adca_w18_r28_pP_L0) C_UW_8e7a8_1adca_w18_r28_pP_L0.OBLS C_UW_8e7a8_1adca_w18_r28_pP_L0.CUTL C_UW_8e7a8_1adca_w18_r28_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8e7a8_1adca_w18_r28_pP_L0.CTX (h_ctabE H)) C_UW_8e7a8_1adca_w18_r28_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8e7a8_1adca_w18_r28_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8e7a8_1adca_p60c2a0_w16_r26_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8e7a8_1adca_p60c2a0_w16_r26_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.CTX C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.PLAN (t_st TE.T_XA_8e7a8_1adca_p60c2a0_w16_r26_pP) C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.OBLS C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.CUTL C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.CTX (h_ctabE H)) C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8e7a8_1adca_p60c2a0_w16_r26_pP.CUTL]; apply Forall_cons; [exact (LN_T_THROW2_ccc04_pP_q499a H)|]; apply Forall_cons; [exact (LN_T_UW_8e7a8_1adca_w18_r28_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_8e7a8_LIBENT_r9_4 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_8e7a8_LIBENT_r9_4).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_8e7a8_LIBENT_r9_4.CTX C_EH_8e7a8_LIBENT_r9_4.PLAN (t_st TL.T_THROW_8e7a8_LIBENT_r9_4) C_EH_8e7a8_LIBENT_r9_4.OBLS C_EH_8e7a8_LIBENT_r9_4.CUTL C_EH_8e7a8_LIBENT_r9_4.WF ITAB_ok (contracts_ok_of SEGS R C_EH_8e7a8_LIBENT_r9_4.CTX (h_ctabE H)) C_EH_8e7a8_LIBENT_r9_4.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_8e7a8_LIBENT_r9_4.CUTL]; apply Forall_cons; [exact (LN_T_XA_8e7a8_1adca_blk_w18_r28_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_8e7a8_1adca_p60c2a0_w16_r26_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_ccc04_f041d_w14_r24_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_ccc04_f041d_w14_r24_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_ccc04_f041d_w14_r24_pv_L0.CTX C_UW_ccc04_f041d_w14_r24_pv_L0.PLAN (t_st TE.T_UW_ccc04_f041d_w14_r24_pv_L0) C_UW_ccc04_f041d_w14_r24_pv_L0.OBLS C_UW_ccc04_f041d_w14_r24_pv_L0.CUTL C_UW_ccc04_f041d_w14_r24_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_ccc04_f041d_w14_r24_pv_L0.CTX (h_ctabE H)) C_UW_ccc04_f041d_w14_r24_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_ccc04_f041d_w14_r24_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_ccc04_f041d_blk_w14_r24_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_ccc04_f041d_blk_w14_r24_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_ccc04_f041d_blk_w14_r24_L0.CTX C_XA_ccc04_f041d_blk_w14_r24_L0.PLAN (t_st TE.T_XA_ccc04_f041d_blk_w14_r24_L0) C_XA_ccc04_f041d_blk_w14_r24_L0.OBLS C_XA_ccc04_f041d_blk_w14_r24_L0.CUTL C_XA_ccc04_f041d_blk_w14_r24_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_ccc04_f041d_blk_w14_r24_L0.CTX (h_ctabE H)) C_XA_ccc04_f041d_blk_w14_r24_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_ccc04_f041d_blk_w14_r24_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_ccc04_f041d_w14_r24_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_ccc04_f041d_w12_r22_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_ccc04_f041d_w12_r22_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_ccc04_f041d_w12_r22_pP_L0.CTX C_UW_ccc04_f041d_w12_r22_pP_L0.PLAN (t_st TE.T_UW_ccc04_f041d_w12_r22_pP_L0) C_UW_ccc04_f041d_w12_r22_pP_L0.OBLS C_UW_ccc04_f041d_w12_r22_pP_L0.CUTL C_UW_ccc04_f041d_w12_r22_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_ccc04_f041d_w12_r22_pP_L0.CTX (h_ctabE H)) C_UW_ccc04_f041d_w12_r22_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_ccc04_f041d_w12_r22_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_ccc04_f041d_p60c2a0_w12_r22_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_ccc04_f041d_p60c2a0_w12_r22_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.CTX C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.PLAN (t_st TE.T_XA_ccc04_f041d_p60c2a0_w12_r22_pP) C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.OBLS C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.CUTL C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.CTX (h_ctabE H)) C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_ccc04_f041d_p60c2a0_w12_r22_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_ccc04_f041d_w12_r22_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_ccc04_LIBENT_r9_3 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_ccc04_LIBENT_r9_3).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_ccc04_LIBENT_r9_3.CTX C_EH_ccc04_LIBENT_r9_3.PLAN (t_st TL.T_THROW_ccc04_LIBENT_r9_3) C_EH_ccc04_LIBENT_r9_3.OBLS C_EH_ccc04_LIBENT_r9_3.CUTL C_EH_ccc04_LIBENT_r9_3.WF ITAB_ok (contracts_ok_of SEGS R C_EH_ccc04_LIBENT_r9_3.CTX (h_ctabE H)) C_EH_ccc04_LIBENT_r9_3.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_ccc04_LIBENT_r9_3.CUTL]; apply Forall_cons; [exact (LN_T_XA_ccc04_f041d_blk_w14_r24_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_ccc04_f041d_p60c2a0_w12_r22_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_LIBGEN_r9 (H : hyps) : LNODE SEGS R N E0 K (t_st DF.T_LIBGEN_r9).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_LIBENT_r9.CTX C_LIBENT_r9.PLAN (t_st DF.T_LIBGEN_r9) C_LIBENT_r9.OBLS C_LIBENT_r9.CUTL C_LIBENT_r9.WF ITAB_ok (contracts_ok_of SEGS R C_LIBENT_r9.CTX (h_ctabL H)) C_LIBENT_r9.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_LIBENT_r9.CUTL]; apply Forall_cons; [exact (LN_T_THROW_8d6b8_LIBENT_r9_1 H)|]; apply Forall_cons; [exact (LN_T_THROW_8d78c_LIBENT_r9_2 H)|]; apply Forall_cons; [exact (LN_T_THROW_8e7a8_LIBENT_r9_4 H)|]; apply Forall_cons; [exact (LN_T_THROW_ccc04_LIBENT_r9_3 H)|]; apply Forall_nil) eq_refl).
Qed.
End A.

Theorem lib_ok_r9 (R : drun) : ctab_ok SEGS R TL.CONTRACTS -> ctab_ok SEGS R TE.CONTRACTS ->
  lib_ok SEGS R (t_st DF.T_LIBGEN_r9) (t_st DF.R_LIBGEN_r9_RET).
Proof.
  intros HL HE. apply lib_ok_of. intros E0 K HPB HRET.
  exact (LN_T_LIBGEN_r9 R E0 K (Hyps R E0 K HPB HL HE HRET)).
Qed.
End LibRunAsan_r9.
