(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.EH Require Import Pool.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2F Require T_Src2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2L Require T_Src2L B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E Require T_Src2E B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib.
Open Scope Z_scope.
Unset Lia Cache.
Module DF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2F.T_Src2F.
Module TL := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2L.T_Src2L.
Module TE := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.T_Src2E.
Module C_EH_1f588_LIBENT_r9_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_1f588_LIBENT_r9_1.
Module C_EH_1f5fc_LIBENT_r9_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_1f5fc_LIBENT_r9_2.
Module C_EH_51130_LIBENT_r9_3 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_51130_LIBENT_r9_3.
Module C_EH_51130_LIBENT_r9_4 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_51130_LIBENT_r9_4.
Module C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.
Module C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.
Module C_UW_1f588_a9686_w4_r11_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f588_a9686_w4_r11_pv_L0.
Module C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.
Module C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.
Module C_UW_1f5fc_04dd4_w5_r12_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f5fc_04dd4_w5_r12_pv_L0.
Module C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.
Module C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.
Module C_UW_51130_0d98c_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_0d98c_w7_r14_pv_L0.
Module C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.
Module C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.
Module C_UW_51130_b9095_w6_r13_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_b9095_w6_r13_pv_L0.
Module C_XA_1f588_a9686_blk_w4_r11_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f588_a9686_blk_w4_r11_L0.
Module C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.
Module C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.
Module C_XA_1f5fc_04dd4_blk_w5_r12_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f5fc_04dd4_blk_w5_r12_L0.
Module C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.
Module C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.
Module C_XA_51130_0d98c_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_0d98c_blk_w7_r14_L0.
Module C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.
Module C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.
Module C_XA_51130_b9095_blk_w6_r13_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_b9095_blk_w6_r13_L0.
Module C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.
Module C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.
Module C_LIBENT_r9 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2L.B_00.C_LIBENT_r9.

Module LibRunSrc_r9.
Definition N : int := 118%uint63.
Section A.
Variable R : drun.
Variables (E0 : env) (K : TSet).
Record hyps : Prop := Hyps {
  h_pb : r_PB R (eb E0);
  h_ctabL : ctab_ok SEGS R TL.CONTRACTS;
  h_ctabE : ctab_ok SEGS R TE.CONTRACTS;
  h_g0 : LNODE SEGS R N E0 K (t_st TL.T_G0_r14o5n0o7n1o1n24o3n2);
  h_ret : LNODE SEGS R N E0 K (t_st DF.R_LIBGEN_r9_RET) }.

Lemma LN_T_UW_1f588_a9686_w4_r11_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f588_a9686_w4_r11_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f588_a9686_w4_r11_pv_L0.CTX C_UW_1f588_a9686_w4_r11_pv_L0.PLAN (t_st TE.T_UW_1f588_a9686_w4_r11_pv_L0) C_UW_1f588_a9686_w4_r11_pv_L0.OBLS _ C_UW_1f588_a9686_w4_r11_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f588_a9686_w4_r11_pv_L0.CTX (h_ctabE H)) C_UW_1f588_a9686_w4_r11_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f588_a9686_w4_r11_pv_L0.CTX c_cuts C_UW_1f588_a9686_w4_r11_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f588_a9686_blk_w4_r11_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f588_a9686_blk_w4_r11_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f588_a9686_blk_w4_r11_L0.CTX C_XA_1f588_a9686_blk_w4_r11_L0.PLAN (t_st TE.T_XA_1f588_a9686_blk_w4_r11_L0) C_XA_1f588_a9686_blk_w4_r11_L0.OBLS _ C_XA_1f588_a9686_blk_w4_r11_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f588_a9686_blk_w4_r11_L0.CTX (h_ctabE H)) C_XA_1f588_a9686_blk_w4_r11_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f588_a9686_blk_w4_r11_L0.CTX c_cuts C_XA_1f588_a9686_blk_w4_r11_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f588_a9686_w4_r11_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.CTX C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0) C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.OBLS _ C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.CTX c_cuts C_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.CTX C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.PLAN (t_st TE.T_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776) C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.OBLS _ C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.CTX (h_ctabE H)) C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.CTX c_cuts C_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f588_a9686_w3_r10_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.CTX C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0) C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.OBLS _ C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.CTX c_cuts C_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.CTX C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.PLAN (t_st TE.T_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449) C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.OBLS _ C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.CTX (h_ctabE H)) C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.CTX c_cuts C_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f588_a9686_w3_r10_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_1f588_LIBENT_r9_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_1f588_LIBENT_r9_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_1f588_LIBENT_r9_1.CTX C_EH_1f588_LIBENT_r9_1.PLAN (t_st TL.T_THROW_1f588_LIBENT_r9_1) C_EH_1f588_LIBENT_r9_1.OBLS _ C_EH_1f588_LIBENT_r9_1.WF ITAB_ok (contracts_ok_of SEGS R C_EH_1f588_LIBENT_r9_1.CTX (h_ctabE H)) C_EH_1f588_LIBENT_r9_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_1f588_LIBENT_r9_1.CTX c_cuts C_EH_1f588_LIBENT_r9_1.CUTS]; apply Forall_cons; [exact (LN_T_XA_1f588_a9686_blk_w4_r11_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_1f588_a9686_p66ae0_w3_r10_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_1f588_a9686_p66ae0_w3_r10_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f5fc_04dd4_w5_r12_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f5fc_04dd4_w5_r12_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f5fc_04dd4_w5_r12_pv_L0.CTX C_UW_1f5fc_04dd4_w5_r12_pv_L0.PLAN (t_st TE.T_UW_1f5fc_04dd4_w5_r12_pv_L0) C_UW_1f5fc_04dd4_w5_r12_pv_L0.OBLS _ C_UW_1f5fc_04dd4_w5_r12_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f5fc_04dd4_w5_r12_pv_L0.CTX (h_ctabE H)) C_UW_1f5fc_04dd4_w5_r12_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f5fc_04dd4_w5_r12_pv_L0.CTX c_cuts C_UW_1f5fc_04dd4_w5_r12_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f5fc_04dd4_blk_w5_r12_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f5fc_04dd4_blk_w5_r12_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f5fc_04dd4_blk_w5_r12_L0.CTX C_XA_1f5fc_04dd4_blk_w5_r12_L0.PLAN (t_st TE.T_XA_1f5fc_04dd4_blk_w5_r12_L0) C_XA_1f5fc_04dd4_blk_w5_r12_L0.OBLS _ C_XA_1f5fc_04dd4_blk_w5_r12_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f5fc_04dd4_blk_w5_r12_L0.CTX (h_ctabE H)) C_XA_1f5fc_04dd4_blk_w5_r12_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f5fc_04dd4_blk_w5_r12_L0.CTX c_cuts C_XA_1f5fc_04dd4_blk_w5_r12_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f5fc_04dd4_w5_r12_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.CTX C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0) C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.OBLS _ C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.CTX c_cuts C_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.CTX C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.PLAN (t_st TE.T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776) C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.OBLS _ C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.CTX (h_ctabE H)) C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.CTX c_cuts C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f5fc_04dd4_w4_r11_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.CTX C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0) C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.OBLS _ C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.CTX c_cuts C_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.CTX C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.PLAN (t_st TE.T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449) C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.OBLS _ C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.CTX (h_ctabE H)) C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.CTX c_cuts C_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f5fc_04dd4_w4_r11_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_1f5fc_LIBENT_r9_2 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_1f5fc_LIBENT_r9_2).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_1f5fc_LIBENT_r9_2.CTX C_EH_1f5fc_LIBENT_r9_2.PLAN (t_st TL.T_THROW_1f5fc_LIBENT_r9_2) C_EH_1f5fc_LIBENT_r9_2.OBLS _ C_EH_1f5fc_LIBENT_r9_2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_1f5fc_LIBENT_r9_2.CTX (h_ctabE H)) C_EH_1f5fc_LIBENT_r9_2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_1f5fc_LIBENT_r9_2.CTX c_cuts C_EH_1f5fc_LIBENT_r9_2.CUTS]; apply Forall_cons; [exact (LN_T_XA_1f5fc_04dd4_blk_w5_r12_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_1f5fc_04dd4_p66ae0_w4_r11_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_b9095_w6_r13_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_b9095_w6_r13_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_b9095_w6_r13_pv_L0.CTX C_UW_51130_b9095_w6_r13_pv_L0.PLAN (t_st TE.T_UW_51130_b9095_w6_r13_pv_L0) C_UW_51130_b9095_w6_r13_pv_L0.OBLS _ C_UW_51130_b9095_w6_r13_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_b9095_w6_r13_pv_L0.CTX (h_ctabE H)) C_UW_51130_b9095_w6_r13_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_b9095_w6_r13_pv_L0.CTX c_cuts C_UW_51130_b9095_w6_r13_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_b9095_blk_w6_r13_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_b9095_blk_w6_r13_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_b9095_blk_w6_r13_L0.CTX C_XA_51130_b9095_blk_w6_r13_L0.PLAN (t_st TE.T_XA_51130_b9095_blk_w6_r13_L0) C_XA_51130_b9095_blk_w6_r13_L0.OBLS _ C_XA_51130_b9095_blk_w6_r13_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_b9095_blk_w6_r13_L0.CTX (h_ctabE H)) C_XA_51130_b9095_blk_w6_r13_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_b9095_blk_w6_r13_L0.CTX c_cuts C_XA_51130_b9095_blk_w6_r13_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_b9095_w6_r13_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.CTX C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0) C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.OBLS _ C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.CTX c_cuts C_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.CTX C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.PLAN (t_st TE.T_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776) C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.OBLS _ C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.CTX (h_ctabE H)) C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.CTX c_cuts C_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_b9095_w5_r12_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.CTX C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0) C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.OBLS _ C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.CTX c_cuts C_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.CTX C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.PLAN (t_st TE.T_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449) C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.OBLS _ C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.CTX (h_ctabE H)) C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.CTX c_cuts C_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_b9095_w5_r12_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_51130_LIBENT_r9_3 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_51130_LIBENT_r9_3).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_51130_LIBENT_r9_3.CTX C_EH_51130_LIBENT_r9_3.PLAN (t_st TL.T_THROW_51130_LIBENT_r9_3) C_EH_51130_LIBENT_r9_3.OBLS _ C_EH_51130_LIBENT_r9_3.WF ITAB_ok (contracts_ok_of SEGS R C_EH_51130_LIBENT_r9_3.CTX (h_ctabE H)) C_EH_51130_LIBENT_r9_3.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_51130_LIBENT_r9_3.CTX c_cuts C_EH_51130_LIBENT_r9_3.CUTS]; apply Forall_cons; [exact (LN_T_XA_51130_b9095_blk_w6_r13_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_b9095_p66ae0_w5_r12_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_b9095_p66ae0_w5_r12_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_0d98c_w7_r14_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_0d98c_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_0d98c_w7_r14_pv_L0.CTX C_UW_51130_0d98c_w7_r14_pv_L0.PLAN (t_st TE.T_UW_51130_0d98c_w7_r14_pv_L0) C_UW_51130_0d98c_w7_r14_pv_L0.OBLS _ C_UW_51130_0d98c_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_0d98c_w7_r14_pv_L0.CTX (h_ctabE H)) C_UW_51130_0d98c_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_0d98c_w7_r14_pv_L0.CTX c_cuts C_UW_51130_0d98c_w7_r14_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_0d98c_blk_w7_r14_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_0d98c_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_0d98c_blk_w7_r14_L0.CTX C_XA_51130_0d98c_blk_w7_r14_L0.PLAN (t_st TE.T_XA_51130_0d98c_blk_w7_r14_L0) C_XA_51130_0d98c_blk_w7_r14_L0.OBLS _ C_XA_51130_0d98c_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_0d98c_blk_w7_r14_L0.CTX (h_ctabE H)) C_XA_51130_0d98c_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_0d98c_blk_w7_r14_L0.CTX c_cuts C_XA_51130_0d98c_blk_w7_r14_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_0d98c_w7_r14_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.CTX C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0) C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.OBLS _ C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.CTX c_cuts C_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.CTX C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.PLAN (t_st TE.T_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776) C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.OBLS _ C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.CTX (h_ctabE H)) C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.CTX c_cuts C_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_0d98c_w6_r13_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.CTX C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0) C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.OBLS _ C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.CTX c_cuts C_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.CTX C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.PLAN (t_st TE.T_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449) C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.OBLS _ C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.CTX (h_ctabE H)) C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.CTX c_cuts C_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_0d98c_w6_r13_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_51130_LIBENT_r9_4 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_51130_LIBENT_r9_4).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_51130_LIBENT_r9_4.CTX C_EH_51130_LIBENT_r9_4.PLAN (t_st TL.T_THROW_51130_LIBENT_r9_4) C_EH_51130_LIBENT_r9_4.OBLS _ C_EH_51130_LIBENT_r9_4.WF ITAB_ok (contracts_ok_of SEGS R C_EH_51130_LIBENT_r9_4.CTX (h_ctabE H)) C_EH_51130_LIBENT_r9_4.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_51130_LIBENT_r9_4.CTX c_cuts C_EH_51130_LIBENT_r9_4.CUTS]; apply Forall_cons; [exact (LN_T_XA_51130_0d98c_blk_w7_r14_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_0d98c_p66ae0_w6_r13_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_0d98c_p66ae0_w6_r13_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_LIBGEN_r9 (H : hyps) : LNODE SEGS R N E0 K (t_st DF.T_LIBGEN_r9).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_LIBENT_r9.CTX C_LIBENT_r9.PLAN (t_st DF.T_LIBGEN_r9) C_LIBENT_r9.OBLS _ C_LIBENT_r9.WF ITAB_ok (contracts_ok_of SEGS R C_LIBENT_r9.CTX (h_ctabL H)) C_LIBENT_r9.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_LIBENT_r9.CTX c_cuts C_LIBENT_r9.CUTS]; apply Forall_cons; [exact (h_g0 H)|]; apply Forall_cons; [exact (LN_T_THROW_1f588_LIBENT_r9_1 H)|]; apply Forall_cons; [exact (LN_T_THROW_1f5fc_LIBENT_r9_2 H)|]; apply Forall_cons; [exact (LN_T_THROW_51130_LIBENT_r9_3 H)|]; apply Forall_cons; [exact (LN_T_THROW_51130_LIBENT_r9_4 H)|]; apply Forall_nil) eq_refl).
Qed.
End A.

Theorem lib_ok_r9 (R : drun) : ctab_ok SEGS R TL.CONTRACTS -> ctab_ok SEGS R TE.CONTRACTS ->
  (forall E0 K, r_PB R (eb E0) -> LNODE SEGS R N E0 K (t_st DF.R_LIBGEN_r9_RET) -> LNODE SEGS R N E0 K (t_st TL.T_G0_r14o5n0o7n1o1n24o3n2)) ->
  lib_ok SEGS R (t_st DF.T_LIBGEN_r9) (t_st DF.R_LIBGEN_r9_RET).
Proof.
  intros HL HE HG0. apply lib_ok_of. intros E0 K HPB HRET.
  exact (LN_T_LIBGEN_r9 R E0 K (Hyps R E0 K HPB HL HE (HG0 E0 K HPB HRET) HRET)).
Qed.
End LibRunSrc_r9.
