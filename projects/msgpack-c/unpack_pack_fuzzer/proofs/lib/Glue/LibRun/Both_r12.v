(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgBoth ItabBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2F Require T_Both2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L Require T_Both2L B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E Require T_Both2E B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib.
Open Scope Z_scope.
Unset Lia Cache.
Module DF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2F.T_Both2F.
Module TL := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L.T_Both2L.
Module TE := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.T_Both2E.
Module C_EH_8e0d0_LIBENT_r12_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_EH_8e0d0_LIBENT_r12_1.
Module C_EH_8e1c8_LIBENT_r12_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_EH_8e1c8_LIBENT_r12_2.
Module C_EH_ced48_LIBENT_r12_3 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_EH_ced48_LIBENT_r12_3.
Module C_EH_ced48_LIBENT_r12_4 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_EH_ced48_LIBENT_r12_4.
Module C_UW_8e0d0_aa8f5_w10_r21_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_8e0d0_aa8f5_w10_r21_pP_L0.
Module C_UW_8e0d0_aa8f5_w12_r23_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_8e0d0_aa8f5_w12_r23_pv_L0.
Module C_UW_8e1c8_af996_w12_r23_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_8e1c8_af996_w12_r23_pP_L0.
Module C_UW_8e1c8_af996_w14_r25_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_8e1c8_af996_w14_r25_pv_L0.
Module C_UW_ced48_f2725_w18_r29_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_ced48_f2725_w18_r29_pP_L0.
Module C_UW_ced48_f2725_w20_r31_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_ced48_f2725_w20_r31_pv_L0.
Module C_UW_ced48_f3c68_w14_r25_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_ced48_f3c68_w14_r25_pP_L0.
Module C_UW_ced48_f3c68_w16_r27_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_UW_ced48_f3c68_w16_r27_pv_L0.
Module C_XA_8e0d0_aa8f5_blk_w12_r23_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_8e0d0_aa8f5_blk_w12_r23_L0.
Module C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.
Module C_XA_8e1c8_af996_blk_w14_r25_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_8e1c8_af996_blk_w14_r25_L0.
Module C_XA_8e1c8_af996_p60e4a0_w12_r23_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.
Module C_XA_ced48_f2725_blk_w20_r31_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_ced48_f2725_blk_w20_r31_L0.
Module C_XA_ced48_f2725_p60e4a0_w18_r29_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_ced48_f2725_p60e4a0_w18_r29_pP.
Module C_XA_ced48_f3c68_blk_w16_r27_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_ced48_f3c68_blk_w16_r27_L0.
Module C_XA_ced48_f3c68_p60e4a0_w14_r25_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2E.B_00.C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.
Module C_LIBENT_r12 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2L.B_00.C_LIBENT_r12.

Module LibRunBoth_r12.
Definition N : int := 186%uint63.
Section A.
Variable R : drun.
Variables (E0 : env) (K : TSet).
Record hyps : Prop := Hyps {
  h_pb : r_PB R (eb E0);
  h_ctabL : ctab_ok SEGS R TL.CONTRACTS;
  h_ctabE : ctab_ok SEGS R TE.CONTRACTS;
  h_g0 : LNODE SEGS R N E0 K (t_st TL.T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0);
  h_ret : LNODE SEGS R N E0 K (t_st DF.R_LIBGEN_r12_RET) }.

Lemma LN_T_UW_8e0d0_aa8f5_w12_r23_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8e0d0_aa8f5_w12_r23_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8e0d0_aa8f5_w12_r23_pv_L0.CTX C_UW_8e0d0_aa8f5_w12_r23_pv_L0.PLAN (t_st TE.T_UW_8e0d0_aa8f5_w12_r23_pv_L0) C_UW_8e0d0_aa8f5_w12_r23_pv_L0.OBLS C_UW_8e0d0_aa8f5_w12_r23_pv_L0.CUTL C_UW_8e0d0_aa8f5_w12_r23_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8e0d0_aa8f5_w12_r23_pv_L0.CTX (h_ctabE H)) C_UW_8e0d0_aa8f5_w12_r23_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8e0d0_aa8f5_w12_r23_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8e0d0_aa8f5_blk_w12_r23_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8e0d0_aa8f5_blk_w12_r23_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8e0d0_aa8f5_blk_w12_r23_L0.CTX C_XA_8e0d0_aa8f5_blk_w12_r23_L0.PLAN (t_st TE.T_XA_8e0d0_aa8f5_blk_w12_r23_L0) C_XA_8e0d0_aa8f5_blk_w12_r23_L0.OBLS C_XA_8e0d0_aa8f5_blk_w12_r23_L0.CUTL C_XA_8e0d0_aa8f5_blk_w12_r23_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8e0d0_aa8f5_blk_w12_r23_L0.CTX (h_ctabE H)) C_XA_8e0d0_aa8f5_blk_w12_r23_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8e0d0_aa8f5_blk_w12_r23_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_8e0d0_aa8f5_w12_r23_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8e0d0_aa8f5_w10_r21_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8e0d0_aa8f5_w10_r21_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8e0d0_aa8f5_w10_r21_pP_L0.CTX C_UW_8e0d0_aa8f5_w10_r21_pP_L0.PLAN (t_st TE.T_UW_8e0d0_aa8f5_w10_r21_pP_L0) C_UW_8e0d0_aa8f5_w10_r21_pP_L0.OBLS C_UW_8e0d0_aa8f5_w10_r21_pP_L0.CUTL C_UW_8e0d0_aa8f5_w10_r21_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8e0d0_aa8f5_w10_r21_pP_L0.CTX (h_ctabE H)) C_UW_8e0d0_aa8f5_w10_r21_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8e0d0_aa8f5_w10_r21_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.CTX C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.PLAN (t_st TE.T_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP) C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.OBLS C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.CUTL C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.CTX (h_ctabE H)) C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_8e0d0_aa8f5_w10_r21_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_8e0d0_LIBENT_r12_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_8e0d0_LIBENT_r12_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_8e0d0_LIBENT_r12_1.CTX C_EH_8e0d0_LIBENT_r12_1.PLAN (t_st TL.T_THROW_8e0d0_LIBENT_r12_1) C_EH_8e0d0_LIBENT_r12_1.OBLS C_EH_8e0d0_LIBENT_r12_1.CUTL C_EH_8e0d0_LIBENT_r12_1.WF ITAB_ok (contracts_ok_of SEGS R C_EH_8e0d0_LIBENT_r12_1.CTX (h_ctabE H)) C_EH_8e0d0_LIBENT_r12_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_8e0d0_LIBENT_r12_1.CUTL]; apply Forall_cons; [exact (LN_T_XA_8e0d0_aa8f5_blk_w12_r23_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_8e0d0_aa8f5_p60e4a0_w10_r21_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8e1c8_af996_w14_r25_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8e1c8_af996_w14_r25_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8e1c8_af996_w14_r25_pv_L0.CTX C_UW_8e1c8_af996_w14_r25_pv_L0.PLAN (t_st TE.T_UW_8e1c8_af996_w14_r25_pv_L0) C_UW_8e1c8_af996_w14_r25_pv_L0.OBLS C_UW_8e1c8_af996_w14_r25_pv_L0.CUTL C_UW_8e1c8_af996_w14_r25_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8e1c8_af996_w14_r25_pv_L0.CTX (h_ctabE H)) C_UW_8e1c8_af996_w14_r25_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8e1c8_af996_w14_r25_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8e1c8_af996_blk_w14_r25_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8e1c8_af996_blk_w14_r25_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8e1c8_af996_blk_w14_r25_L0.CTX C_XA_8e1c8_af996_blk_w14_r25_L0.PLAN (t_st TE.T_XA_8e1c8_af996_blk_w14_r25_L0) C_XA_8e1c8_af996_blk_w14_r25_L0.OBLS C_XA_8e1c8_af996_blk_w14_r25_L0.CUTL C_XA_8e1c8_af996_blk_w14_r25_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8e1c8_af996_blk_w14_r25_L0.CTX (h_ctabE H)) C_XA_8e1c8_af996_blk_w14_r25_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8e1c8_af996_blk_w14_r25_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_8e1c8_af996_w14_r25_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_8e1c8_af996_w12_r23_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_8e1c8_af996_w12_r23_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_8e1c8_af996_w12_r23_pP_L0.CTX C_UW_8e1c8_af996_w12_r23_pP_L0.PLAN (t_st TE.T_UW_8e1c8_af996_w12_r23_pP_L0) C_UW_8e1c8_af996_w12_r23_pP_L0.OBLS C_UW_8e1c8_af996_w12_r23_pP_L0.CUTL C_UW_8e1c8_af996_w12_r23_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_8e1c8_af996_w12_r23_pP_L0.CTX (h_ctabE H)) C_UW_8e1c8_af996_w12_r23_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_8e1c8_af996_w12_r23_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_8e1c8_af996_p60e4a0_w12_r23_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_8e1c8_af996_p60e4a0_w12_r23_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.CTX C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.PLAN (t_st TE.T_XA_8e1c8_af996_p60e4a0_w12_r23_pP) C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.OBLS C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.CUTL C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.CTX (h_ctabE H)) C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_8e1c8_af996_p60e4a0_w12_r23_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_8e1c8_af996_w12_r23_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_8e1c8_LIBENT_r12_2 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_8e1c8_LIBENT_r12_2).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_8e1c8_LIBENT_r12_2.CTX C_EH_8e1c8_LIBENT_r12_2.PLAN (t_st TL.T_THROW_8e1c8_LIBENT_r12_2) C_EH_8e1c8_LIBENT_r12_2.OBLS C_EH_8e1c8_LIBENT_r12_2.CUTL C_EH_8e1c8_LIBENT_r12_2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_8e1c8_LIBENT_r12_2.CTX (h_ctabE H)) C_EH_8e1c8_LIBENT_r12_2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_8e1c8_LIBENT_r12_2.CUTL]; apply Forall_cons; [exact (LN_T_XA_8e1c8_af996_blk_w14_r25_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_8e1c8_af996_p60e4a0_w12_r23_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_ced48_f3c68_w16_r27_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_ced48_f3c68_w16_r27_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_ced48_f3c68_w16_r27_pv_L0.CTX C_UW_ced48_f3c68_w16_r27_pv_L0.PLAN (t_st TE.T_UW_ced48_f3c68_w16_r27_pv_L0) C_UW_ced48_f3c68_w16_r27_pv_L0.OBLS C_UW_ced48_f3c68_w16_r27_pv_L0.CUTL C_UW_ced48_f3c68_w16_r27_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_ced48_f3c68_w16_r27_pv_L0.CTX (h_ctabE H)) C_UW_ced48_f3c68_w16_r27_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_ced48_f3c68_w16_r27_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_ced48_f3c68_blk_w16_r27_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_ced48_f3c68_blk_w16_r27_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_ced48_f3c68_blk_w16_r27_L0.CTX C_XA_ced48_f3c68_blk_w16_r27_L0.PLAN (t_st TE.T_XA_ced48_f3c68_blk_w16_r27_L0) C_XA_ced48_f3c68_blk_w16_r27_L0.OBLS C_XA_ced48_f3c68_blk_w16_r27_L0.CUTL C_XA_ced48_f3c68_blk_w16_r27_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_ced48_f3c68_blk_w16_r27_L0.CTX (h_ctabE H)) C_XA_ced48_f3c68_blk_w16_r27_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_ced48_f3c68_blk_w16_r27_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_ced48_f3c68_w16_r27_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_ced48_f3c68_w14_r25_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_ced48_f3c68_w14_r25_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_ced48_f3c68_w14_r25_pP_L0.CTX C_UW_ced48_f3c68_w14_r25_pP_L0.PLAN (t_st TE.T_UW_ced48_f3c68_w14_r25_pP_L0) C_UW_ced48_f3c68_w14_r25_pP_L0.OBLS C_UW_ced48_f3c68_w14_r25_pP_L0.CUTL C_UW_ced48_f3c68_w14_r25_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_ced48_f3c68_w14_r25_pP_L0.CTX (h_ctabE H)) C_UW_ced48_f3c68_w14_r25_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_ced48_f3c68_w14_r25_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_ced48_f3c68_p60e4a0_w14_r25_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_ced48_f3c68_p60e4a0_w14_r25_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.CTX C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.PLAN (t_st TE.T_XA_ced48_f3c68_p60e4a0_w14_r25_pP) C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.OBLS C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.CUTL C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.CTX (h_ctabE H)) C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_ced48_f3c68_p60e4a0_w14_r25_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_ced48_f3c68_w14_r25_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_ced48_LIBENT_r12_3 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_ced48_LIBENT_r12_3).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_ced48_LIBENT_r12_3.CTX C_EH_ced48_LIBENT_r12_3.PLAN (t_st TL.T_THROW_ced48_LIBENT_r12_3) C_EH_ced48_LIBENT_r12_3.OBLS C_EH_ced48_LIBENT_r12_3.CUTL C_EH_ced48_LIBENT_r12_3.WF ITAB_ok (contracts_ok_of SEGS R C_EH_ced48_LIBENT_r12_3.CTX (h_ctabE H)) C_EH_ced48_LIBENT_r12_3.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_ced48_LIBENT_r12_3.CUTL]; apply Forall_cons; [exact (LN_T_XA_ced48_f3c68_blk_w16_r27_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_ced48_f3c68_p60e4a0_w14_r25_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_ced48_f2725_w20_r31_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_ced48_f2725_w20_r31_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_ced48_f2725_w20_r31_pv_L0.CTX C_UW_ced48_f2725_w20_r31_pv_L0.PLAN (t_st TE.T_UW_ced48_f2725_w20_r31_pv_L0) C_UW_ced48_f2725_w20_r31_pv_L0.OBLS C_UW_ced48_f2725_w20_r31_pv_L0.CUTL C_UW_ced48_f2725_w20_r31_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_ced48_f2725_w20_r31_pv_L0.CTX (h_ctabE H)) C_UW_ced48_f2725_w20_r31_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_ced48_f2725_w20_r31_pv_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_ced48_f2725_blk_w20_r31_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_ced48_f2725_blk_w20_r31_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_ced48_f2725_blk_w20_r31_L0.CTX C_XA_ced48_f2725_blk_w20_r31_L0.PLAN (t_st TE.T_XA_ced48_f2725_blk_w20_r31_L0) C_XA_ced48_f2725_blk_w20_r31_L0.OBLS C_XA_ced48_f2725_blk_w20_r31_L0.CUTL C_XA_ced48_f2725_blk_w20_r31_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_ced48_f2725_blk_w20_r31_L0.CTX (h_ctabE H)) C_XA_ced48_f2725_blk_w20_r31_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_ced48_f2725_blk_w20_r31_L0.CUTL]; apply Forall_cons; [exact (LN_T_UW_ced48_f2725_w20_r31_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_ced48_f2725_w18_r29_pP_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_ced48_f2725_w18_r29_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_ced48_f2725_w18_r29_pP_L0.CTX C_UW_ced48_f2725_w18_r29_pP_L0.PLAN (t_st TE.T_UW_ced48_f2725_w18_r29_pP_L0) C_UW_ced48_f2725_w18_r29_pP_L0.OBLS C_UW_ced48_f2725_w18_r29_pP_L0.CUTL C_UW_ced48_f2725_w18_r29_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_ced48_f2725_w18_r29_pP_L0.CTX (h_ctabE H)) C_UW_ced48_f2725_w18_r29_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_UW_ced48_f2725_w18_r29_pP_L0.CUTL]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_ced48_f2725_p60e4a0_w18_r29_pP (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_ced48_f2725_p60e4a0_w18_r29_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_ced48_f2725_p60e4a0_w18_r29_pP.CTX C_XA_ced48_f2725_p60e4a0_w18_r29_pP.PLAN (t_st TE.T_XA_ced48_f2725_p60e4a0_w18_r29_pP) C_XA_ced48_f2725_p60e4a0_w18_r29_pP.OBLS C_XA_ced48_f2725_p60e4a0_w18_r29_pP.CUTL C_XA_ced48_f2725_p60e4a0_w18_r29_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_ced48_f2725_p60e4a0_w18_r29_pP.CTX (h_ctabE H)) C_XA_ced48_f2725_p60e4a0_w18_r29_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_XA_ced48_f2725_p60e4a0_w18_r29_pP.CUTL]; apply Forall_cons; [exact (LN_T_UW_ced48_f2725_w18_r29_pP_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_ced48_LIBENT_r12_4 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_ced48_LIBENT_r12_4).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_ced48_LIBENT_r12_4.CTX C_EH_ced48_LIBENT_r12_4.PLAN (t_st TL.T_THROW_ced48_LIBENT_r12_4) C_EH_ced48_LIBENT_r12_4.OBLS C_EH_ced48_LIBENT_r12_4.CUTL C_EH_ced48_LIBENT_r12_4.WF ITAB_ok (contracts_ok_of SEGS R C_EH_ced48_LIBENT_r12_4.CTX (h_ctabE H)) C_EH_ced48_LIBENT_r12_4.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_EH_ced48_LIBENT_r12_4.CUTL]; apply Forall_cons; [exact (LN_T_XA_ced48_f2725_blk_w20_r31_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_ced48_f2725_p60e4a0_w18_r29_pP H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_LIBGEN_r12 (H : hyps) : LNODE SEGS R N E0 K (t_st DF.T_LIBGEN_r12).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_LIBENT_r12.CTX C_LIBENT_r12.PLAN (t_st DF.T_LIBGEN_r12) C_LIBENT_r12.OBLS C_LIBENT_r12.CUTL C_LIBENT_r12.WF ITAB_ok (contracts_ok_of SEGS R C_LIBENT_r12.CTX (h_ctabL H)) C_LIBENT_r12.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbv delta [C_LIBENT_r12.CUTL]; apply Forall_cons; [exact (h_g0 H)|]; apply Forall_cons; [exact (LN_T_THROW_8e0d0_LIBENT_r12_1 H)|]; apply Forall_cons; [exact (LN_T_THROW_8e1c8_LIBENT_r12_2 H)|]; apply Forall_cons; [exact (LN_T_THROW_ced48_LIBENT_r12_3 H)|]; apply Forall_cons; [exact (LN_T_THROW_ced48_LIBENT_r12_4 H)|]; apply Forall_nil) eq_refl).
Qed.
End A.

Theorem lib_ok_r12 (R : drun) : ctab_ok SEGS R TL.CONTRACTS -> ctab_ok SEGS R TE.CONTRACTS ->
  (forall E0 K, r_PB R (eb E0) -> LNODE SEGS R N E0 K (t_st DF.R_LIBGEN_r12_RET) -> LNODE SEGS R N E0 K (t_st TL.T_G0_r31o5n0o1n63o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0)) ->
  lib_ok SEGS R (t_st DF.T_LIBGEN_r12) (t_st DF.R_LIBGEN_r12_RET).
Proof.
  intros HL HE HG0. apply lib_ok_of. intros E0 K HPB HRET.
  exact (LN_T_LIBGEN_r12 R E0 K (Hyps R E0 K HPB HL HE (HG0 E0 K HPB HRET) HRET)).
Qed.
End LibRunBoth_r12.
