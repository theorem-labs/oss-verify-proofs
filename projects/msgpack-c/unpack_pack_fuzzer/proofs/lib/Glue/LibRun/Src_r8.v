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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E Require T_Src2E B_00 B_01.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib.
Open Scope Z_scope.
Unset Lia Cache.
Module DF := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2F.T_Src2F.
Module TL := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2L.T_Src2L.
Module TE := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.T_Src2E.
Module C_EH_1f588_LIBENT_r8_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_1f588_LIBENT_r8_1.
Module C_EH_1f5fc_LIBENT_r8_2 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_1f5fc_LIBENT_r8_2.
Module C_EH_1fb38_LIBENT_r8_4 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_1fb38_LIBENT_r8_4.
Module C_EH_51130_LIBENT_r8_3 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_EH_51130_LIBENT_r8_3.
Module C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.
Module C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.
Module C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.
Module C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.
Module C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.
Module C_UW_1f588_74b1c_w3_r10_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f588_74b1c_w3_r10_pv_L0.
Module C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.
Module C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.
Module C_UW_1f5fc_6c8de_w4_r11_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1f5fc_6c8de_w4_r11_pv_L0.
Module C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.
Module C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.
Module C_UW_1fb38_b864c_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_1fb38_b864c_w7_r14_pv_L0.
Module C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.
Module C_UW_51130_27549_w6_r13_p3h66a3cc132_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.
Module C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.
Module C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.
Module C_UW_51130_52946_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_52946_w7_r14_pv_L0.
Module C_UW_51130_a364e_w5_r12_p3h6697cc113_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.
Module C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.
Module C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.
Module C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.
Module C_UW_51130_e7aad_w5_r12_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_UW_51130_e7aad_w5_r12_pv_L0.
Module C_XA_1f588_74b1c_blk_w3_r10_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f588_74b1c_blk_w3_r10_L0.
Module C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.
Module C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.
Module C_XA_1f5fc_6c8de_blk_w4_r11_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f5fc_6c8de_blk_w4_r11_L0.
Module C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.
Module C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.
Module C_XA_1fb38_b864c_blk_w6_r13_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1fb38_b864c_blk_w6_r13_L0.
Module C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.
Module C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.
Module C_XA_51130_27549_blk_w6_r13_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_27549_blk_w6_r13_L0.
Module C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.
Module C_XA_51130_52946_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_XA_51130_52946_blk_w7_r14_L0.
Module C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.
Module C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.
Module C_XA_51130_a364e_blk_w6_r13_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_XA_51130_a364e_blk_w6_r13_L0.
Module C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_01.C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.
Module C_XA_51130_e7aad_blk_w5_r12_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_e7aad_blk_w5_r12_L0.
Module C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.
Module C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2E.B_00.C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.
Module C_LIBENT_r8 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2L.B_00.C_LIBENT_r8.

Module LibRunSrc_r8.
Definition N : int := 119%uint63.
Section A.
Variable R : drun.
Variables (E0 : env) (K : TSet).
Record hyps : Prop := Hyps {
  h_pb : r_PB R (eb E0);
  h_ctabL : ctab_ok SEGS R TL.CONTRACTS;
  h_ctabE : ctab_ok SEGS R TE.CONTRACTS;
  h_ret : LNODE SEGS R N E0 K (t_st DF.R_LIBGEN_r8_RET) }.

Lemma LN_T_UW_1f588_74b1c_w3_r10_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f588_74b1c_w3_r10_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f588_74b1c_w3_r10_pv_L0.CTX C_UW_1f588_74b1c_w3_r10_pv_L0.PLAN (t_st TE.T_UW_1f588_74b1c_w3_r10_pv_L0) C_UW_1f588_74b1c_w3_r10_pv_L0.OBLS _ C_UW_1f588_74b1c_w3_r10_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f588_74b1c_w3_r10_pv_L0.CTX (h_ctabE H)) C_UW_1f588_74b1c_w3_r10_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f588_74b1c_w3_r10_pv_L0.CTX c_cuts C_UW_1f588_74b1c_w3_r10_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f588_74b1c_blk_w3_r10_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f588_74b1c_blk_w3_r10_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f588_74b1c_blk_w3_r10_L0.CTX C_XA_1f588_74b1c_blk_w3_r10_L0.PLAN (t_st TE.T_XA_1f588_74b1c_blk_w3_r10_L0) C_XA_1f588_74b1c_blk_w3_r10_L0.OBLS _ C_XA_1f588_74b1c_blk_w3_r10_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f588_74b1c_blk_w3_r10_L0.CTX (h_ctabE H)) C_XA_1f588_74b1c_blk_w3_r10_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f588_74b1c_blk_w3_r10_L0.CTX c_cuts C_XA_1f588_74b1c_blk_w3_r10_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f588_74b1c_w3_r10_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.CTX C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0) C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.OBLS _ C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.CTX c_cuts C_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.CTX C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.PLAN (t_st TE.T_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776) C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.OBLS _ C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.CTX (h_ctabE H)) C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.CTX c_cuts C_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f588_74b1c_w2_r9_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.CTX C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0) C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.OBLS _ C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.CTX c_cuts C_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.CTX C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.PLAN (t_st TE.T_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449) C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.OBLS _ C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.CTX (h_ctabE H)) C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.CTX c_cuts C_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f588_74b1c_w2_r9_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_1f588_LIBENT_r8_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_1f588_LIBENT_r8_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_1f588_LIBENT_r8_1.CTX C_EH_1f588_LIBENT_r8_1.PLAN (t_st TL.T_THROW_1f588_LIBENT_r8_1) C_EH_1f588_LIBENT_r8_1.OBLS _ C_EH_1f588_LIBENT_r8_1.WF ITAB_ok (contracts_ok_of SEGS R C_EH_1f588_LIBENT_r8_1.CTX (h_ctabE H)) C_EH_1f588_LIBENT_r8_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_1f588_LIBENT_r8_1.CTX c_cuts C_EH_1f588_LIBENT_r8_1.CUTS]; apply Forall_cons; [exact (LN_T_XA_1f588_74b1c_blk_w3_r10_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_1f588_74b1c_p66ae0_w2_r9_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_1f588_74b1c_p66ae0_w2_r9_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f5fc_6c8de_w4_r11_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f5fc_6c8de_w4_r11_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f5fc_6c8de_w4_r11_pv_L0.CTX C_UW_1f5fc_6c8de_w4_r11_pv_L0.PLAN (t_st TE.T_UW_1f5fc_6c8de_w4_r11_pv_L0) C_UW_1f5fc_6c8de_w4_r11_pv_L0.OBLS _ C_UW_1f5fc_6c8de_w4_r11_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f5fc_6c8de_w4_r11_pv_L0.CTX (h_ctabE H)) C_UW_1f5fc_6c8de_w4_r11_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f5fc_6c8de_w4_r11_pv_L0.CTX c_cuts C_UW_1f5fc_6c8de_w4_r11_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f5fc_6c8de_blk_w4_r11_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f5fc_6c8de_blk_w4_r11_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f5fc_6c8de_blk_w4_r11_L0.CTX C_XA_1f5fc_6c8de_blk_w4_r11_L0.PLAN (t_st TE.T_XA_1f5fc_6c8de_blk_w4_r11_L0) C_XA_1f5fc_6c8de_blk_w4_r11_L0.OBLS _ C_XA_1f5fc_6c8de_blk_w4_r11_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f5fc_6c8de_blk_w4_r11_L0.CTX (h_ctabE H)) C_XA_1f5fc_6c8de_blk_w4_r11_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f5fc_6c8de_blk_w4_r11_L0.CTX c_cuts C_XA_1f5fc_6c8de_blk_w4_r11_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f5fc_6c8de_w4_r11_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.CTX C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0) C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.OBLS _ C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.CTX c_cuts C_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.CTX C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.PLAN (t_st TE.T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776) C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.OBLS _ C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.CTX (h_ctabE H)) C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.CTX c_cuts C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f5fc_6c8de_w3_r10_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.CTX C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0) C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.OBLS _ C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.CTX c_cuts C_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.CTX C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.PLAN (t_st TE.T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449) C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.OBLS _ C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.CTX (h_ctabE H)) C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.CTX c_cuts C_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_1f5fc_6c8de_w3_r10_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_1f5fc_LIBENT_r8_2 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_1f5fc_LIBENT_r8_2).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_1f5fc_LIBENT_r8_2.CTX C_EH_1f5fc_LIBENT_r8_2.PLAN (t_st TL.T_THROW_1f5fc_LIBENT_r8_2) C_EH_1f5fc_LIBENT_r8_2.OBLS _ C_EH_1f5fc_LIBENT_r8_2.WF ITAB_ok (contracts_ok_of SEGS R C_EH_1f5fc_LIBENT_r8_2.CTX (h_ctabE H)) C_EH_1f5fc_LIBENT_r8_2.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_1f5fc_LIBENT_r8_2.CTX c_cuts C_EH_1f5fc_LIBENT_r8_2.CUTS]; apply Forall_cons; [exact (LN_T_XA_1f5fc_6c8de_blk_w4_r11_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_1f5fc_6c8de_p66ae0_w3_r10_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_52946_w7_r14_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_52946_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_52946_w7_r14_pv_L0.CTX C_UW_51130_52946_w7_r14_pv_L0.PLAN (t_st TE.T_UW_51130_52946_w7_r14_pv_L0) C_UW_51130_52946_w7_r14_pv_L0.OBLS _ C_UW_51130_52946_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_52946_w7_r14_pv_L0.CTX (h_ctabE H)) C_UW_51130_52946_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_52946_w7_r14_pv_L0.CTX c_cuts C_UW_51130_52946_w7_r14_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_52946_blk_w7_r14_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_52946_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_52946_blk_w7_r14_L0.CTX C_XA_51130_52946_blk_w7_r14_L0.PLAN (t_st TE.T_XA_51130_52946_blk_w7_r14_L0) C_XA_51130_52946_blk_w7_r14_L0.OBLS _ C_XA_51130_52946_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_52946_blk_w7_r14_L0.CTX (h_ctabE H)) C_XA_51130_52946_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_52946_blk_w7_r14_L0.CTX c_cuts C_XA_51130_52946_blk_w7_r14_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_52946_w7_r14_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_52946_w6_r13_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_52946_w6_r13_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.CTX C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_51130_52946_w6_r13_p3h6697cc5fb_L0) C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.OBLS _ C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.CTX c_cuts C_UW_51130_52946_w6_r13_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.CTX C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.PLAN (t_st TE.T_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776) C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.OBLS _ C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.CTX (h_ctabE H)) C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.CTX c_cuts C_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_52946_w6_r13_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.CTX C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0) C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.OBLS _ C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.CTX c_cuts C_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.CTX C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.PLAN (t_st TE.T_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449) C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.OBLS _ C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.CTX (h_ctabE H)) C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.CTX c_cuts C_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_52946_w6_r13_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.CTX C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.PLAN (t_st TE.T_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1) C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.OBLS _ C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.CTX (h_ctabE H)) C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.CTX c_cuts C_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1.CUTS]; apply Forall_cons; [exact (LN_T_XA_51130_52946_blk_w7_r14_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_52946_p66ae0_w6_r13_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_52946_p66ae0_w6_r13_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1fb38_b864c_w7_r14_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1fb38_b864c_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1fb38_b864c_w7_r14_pv_L0.CTX C_UW_1fb38_b864c_w7_r14_pv_L0.PLAN (t_st TE.T_UW_1fb38_b864c_w7_r14_pv_L0) C_UW_1fb38_b864c_w7_r14_pv_L0.OBLS _ C_UW_1fb38_b864c_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1fb38_b864c_w7_r14_pv_L0.CTX (h_ctabE H)) C_UW_1fb38_b864c_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1fb38_b864c_w7_r14_pv_L0.CTX c_cuts C_UW_1fb38_b864c_w7_r14_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1fb38_b864c_blk_w6_r13_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1fb38_b864c_blk_w6_r13_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1fb38_b864c_blk_w6_r13_L0.CTX C_XA_1fb38_b864c_blk_w6_r13_L0.PLAN (t_st TE.T_XA_1fb38_b864c_blk_w6_r13_L0) C_XA_1fb38_b864c_blk_w6_r13_L0.OBLS _ C_XA_1fb38_b864c_blk_w6_r13_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1fb38_b864c_blk_w6_r13_L0.CTX (h_ctabE H)) C_XA_1fb38_b864c_blk_w6_r13_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1fb38_b864c_blk_w6_r13_L0.CTX c_cuts C_XA_1fb38_b864c_blk_w6_r13_L0.CUTS]; apply Forall_cons; [exact (LN_T_THROW_n51130_XA_1fb38_b864c_blk_w6_r13_L0_1 H)|]; apply Forall_cons; [exact (LN_T_UW_1fb38_b864c_w7_r14_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_a364e_w6_r13_p3h6697cc68b_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_a364e_w6_r13_p3h6697cc68b_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.CTX C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.PLAN (t_st TE.T_UW_51130_a364e_w6_r13_p3h6697cc68b_L0) C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.OBLS _ C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.CTX (h_ctabE H)) C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.CTX c_cuts C_UW_51130_a364e_w6_r13_p3h6697cc68b_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_a364e_blk_w6_r13_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_a364e_blk_w6_r13_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_a364e_blk_w6_r13_L0.CTX C_XA_51130_a364e_blk_w6_r13_L0.PLAN (t_st TE.T_XA_51130_a364e_blk_w6_r13_L0) C_XA_51130_a364e_blk_w6_r13_L0.OBLS _ C_XA_51130_a364e_blk_w6_r13_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_a364e_blk_w6_r13_L0.CTX (h_ctabE H)) C_XA_51130_a364e_blk_w6_r13_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_a364e_blk_w6_r13_L0.CTX c_cuts C_XA_51130_a364e_blk_w6_r13_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_a364e_w6_r13_p3h6697cc68b_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_a364e_w5_r12_p3h6697cc113_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_a364e_w5_r12_p3h6697cc113_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.CTX C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.PLAN (t_st TE.T_UW_51130_a364e_w5_r12_p3h6697cc113_L0) C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.OBLS _ C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.CTX (h_ctabE H)) C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.CTX c_cuts C_UW_51130_a364e_w5_r12_p3h6697cc113_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.CTX C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.PLAN (t_st TE.T_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d) C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.OBLS _ C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.CTX (h_ctabE H)) C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.CTX c_cuts C_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_a364e_w5_r12_p3h6697cc113_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.CTX C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.PLAN (t_st TE.T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1) C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.OBLS _ C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.CTX (h_ctabE H)) C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.CTX c_cuts C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1.CUTS]; apply Forall_cons; [exact (LN_T_XA_51130_a364e_blk_w6_r13_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_a364e_p66a40_w5_r12_p3h6697cc99d H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.CTX C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.PLAN (t_st TE.T_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0) C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.OBLS _ C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.CTX (h_ctabE H)) C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.CTX c_cuts C_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.CTX C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.PLAN (t_st TE.T_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776) C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.OBLS _ C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.CTX (h_ctabE H)) C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.CTX c_cuts C_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776_1 H)|]; apply Forall_cons; [exact (LN_T_UW_1fb38_b864c_w6_r13_p3h6697ccedd_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_27549_w6_r13_p3h66a3cc132_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_27549_w6_r13_p3h66a3cc132_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.CTX C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.PLAN (t_st TE.T_UW_51130_27549_w6_r13_p3h66a3cc132_L0) C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.OBLS _ C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.CTX (h_ctabE H)) C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.CTX c_cuts C_UW_51130_27549_w6_r13_p3h66a3cc132_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_27549_blk_w6_r13_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_27549_blk_w6_r13_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_27549_blk_w6_r13_L0.CTX C_XA_51130_27549_blk_w6_r13_L0.PLAN (t_st TE.T_XA_51130_27549_blk_w6_r13_L0) C_XA_51130_27549_blk_w6_r13_L0.OBLS _ C_XA_51130_27549_blk_w6_r13_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_27549_blk_w6_r13_L0.CTX (h_ctabE H)) C_XA_51130_27549_blk_w6_r13_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_27549_blk_w6_r13_L0.CTX c_cuts C_XA_51130_27549_blk_w6_r13_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_27549_w6_r13_p3h66a3cc132_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_27549_w5_r12_p3h6697ccc7a_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_27549_w5_r12_p3h6697ccc7a_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.CTX C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.PLAN (t_st TE.T_UW_51130_27549_w5_r12_p3h6697ccc7a_L0) C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.OBLS _ C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.CTX (h_ctabE H)) C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.CTX c_cuts C_UW_51130_27549_w5_r12_p3h6697ccc7a_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_27549_p66a40_w5_r12_p3h6697cc132 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_27549_p66a40_w5_r12_p3h6697cc132).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.CTX C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.PLAN (t_st TE.T_XA_51130_27549_p66a40_w5_r12_p3h6697cc132) C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.OBLS _ C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.CTX (h_ctabE H)) C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.CTX c_cuts C_XA_51130_27549_p66a40_w5_r12_p3h6697cc132.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_27549_w5_r12_p3h6697ccc7a_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.CTX C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.PLAN (t_st TE.T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1) C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.OBLS _ C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.CTX (h_ctabE H)) C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.CTX c_cuts C_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1.CUTS]; apply Forall_cons; [exact (LN_T_XA_51130_27549_blk_w6_r13_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_27549_p66a40_w5_r12_p3h6697cc132 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.CTX C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.PLAN (t_st TE.T_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0) C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.OBLS _ C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.CTX (h_ctabE H)) C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.CTX c_cuts C_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.CTX C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.PLAN (t_st TE.T_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449) C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.OBLS _ C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.CTX (h_ctabE H)) C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.CTX c_cuts C_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_THROW_n51130_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449_1 H)|]; apply Forall_cons; [exact (LN_T_UW_1fb38_b864c_w6_r13_p3h66a3cca88_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_1fb38_LIBENT_r8_4 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_1fb38_LIBENT_r8_4).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_1fb38_LIBENT_r8_4.CTX C_EH_1fb38_LIBENT_r8_4.PLAN (t_st TL.T_THROW_1fb38_LIBENT_r8_4) C_EH_1fb38_LIBENT_r8_4.OBLS _ C_EH_1fb38_LIBENT_r8_4.WF ITAB_ok (contracts_ok_of SEGS R C_EH_1fb38_LIBENT_r8_4.CTX (h_ctabE H)) C_EH_1fb38_LIBENT_r8_4.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_1fb38_LIBENT_r8_4.CTX c_cuts C_EH_1fb38_LIBENT_r8_4.CUTS]; apply Forall_cons; [exact (LN_T_XA_1fb38_b864c_blk_w6_r13_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_1fb38_b864c_p66ae0_w5_r12_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_1fb38_b864c_p66ae0_w5_r12_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_e7aad_w5_r12_pv_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_e7aad_w5_r12_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_e7aad_w5_r12_pv_L0.CTX C_UW_51130_e7aad_w5_r12_pv_L0.PLAN (t_st TE.T_UW_51130_e7aad_w5_r12_pv_L0) C_UW_51130_e7aad_w5_r12_pv_L0.OBLS _ C_UW_51130_e7aad_w5_r12_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_e7aad_w5_r12_pv_L0.CTX (h_ctabE H)) C_UW_51130_e7aad_w5_r12_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_e7aad_w5_r12_pv_L0.CTX c_cuts C_UW_51130_e7aad_w5_r12_pv_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_e7aad_blk_w5_r12_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_e7aad_blk_w5_r12_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_e7aad_blk_w5_r12_L0.CTX C_XA_51130_e7aad_blk_w5_r12_L0.PLAN (t_st TE.T_XA_51130_e7aad_blk_w5_r12_L0) C_XA_51130_e7aad_blk_w5_r12_L0.OBLS _ C_XA_51130_e7aad_blk_w5_r12_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_e7aad_blk_w5_r12_L0.CTX (h_ctabE H)) C_XA_51130_e7aad_blk_w5_r12_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_e7aad_blk_w5_r12_L0.CTX c_cuts C_XA_51130_e7aad_blk_w5_r12_L0.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_e7aad_w5_r12_pv_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.CTX C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.PLAN (t_st TE.T_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0) C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.OBLS _ C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.CTX (h_ctabE H)) C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.CTX c_cuts C_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.CTX C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.PLAN (t_st TE.T_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776) C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.OBLS _ C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.CTX (h_ctabE H)) C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.CTX c_cuts C_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_e7aad_w4_r11_p3h6697cc5fb_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.CTX C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.PLAN (t_st TE.T_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0) C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.OBLS _ C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.CTX (h_ctabE H)) C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.CTX c_cuts C_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0.CUTS]; apply Forall_cons; [exact (h_ret H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449 (H : hyps) : LNODE SEGS R N E0 K (t_st TE.T_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.CTX C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.PLAN (t_st TE.T_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449) C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.OBLS _ C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.WF ITAB_ok (contracts_ok_of SEGS R C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.CTX (h_ctabE H)) C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.CTX c_cuts C_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449.CUTS]; apply Forall_cons; [exact (LN_T_UW_51130_e7aad_w4_r11_p3h66a3cc7f7_L0 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_THROW_51130_LIBENT_r8_3 (H : hyps) : LNODE SEGS R N E0 K (t_st TL.T_THROW_51130_LIBENT_r8_3).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_EH_51130_LIBENT_r8_3.CTX C_EH_51130_LIBENT_r8_3.PLAN (t_st TL.T_THROW_51130_LIBENT_r8_3) C_EH_51130_LIBENT_r8_3.OBLS _ C_EH_51130_LIBENT_r8_3.WF ITAB_ok (contracts_ok_of SEGS R C_EH_51130_LIBENT_r8_3.CTX (h_ctabE H)) C_EH_51130_LIBENT_r8_3.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_EH_51130_LIBENT_r8_3.CTX c_cuts C_EH_51130_LIBENT_r8_3.CUTS]; apply Forall_cons; [exact (LN_T_XA_51130_e7aad_blk_w5_r12_L0 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_e7aad_p66ae0_w4_r11_p3h6697cc776 H)|]; apply Forall_cons; [exact (LN_T_XA_51130_e7aad_p66ae0_w4_r11_p3h66a3cc449 H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_T_LIBGEN_r8 (H : hyps) : LNODE SEGS R N E0 K (t_st DF.T_LIBGEN_r8).
Proof.
  apply (lnode_cert SEGS R N E0 K (h_pb H) C_LIBENT_r8.CTX C_LIBENT_r8.PLAN (t_st DF.T_LIBGEN_r8) C_LIBENT_r8.OBLS _ C_LIBENT_r8.WF ITAB_ok (contracts_ok_of SEGS R C_LIBENT_r8.CTX (h_ctabL H)) C_LIBENT_r8.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn [C_LIBENT_r8.CTX c_cuts C_LIBENT_r8.CUTS]; apply Forall_cons; [exact (LN_T_THROW_1f588_LIBENT_r8_1 H)|]; apply Forall_cons; [exact (LN_T_THROW_1f5fc_LIBENT_r8_2 H)|]; apply Forall_cons; [exact (LN_T_THROW_1fb38_LIBENT_r8_4 H)|]; apply Forall_cons; [exact (LN_T_THROW_51130_LIBENT_r8_3 H)|]; apply Forall_nil) eq_refl).
Qed.
End A.

Theorem lib_ok_r8 (R : drun) : ctab_ok SEGS R TL.CONTRACTS -> ctab_ok SEGS R TE.CONTRACTS ->
  lib_ok SEGS R (t_st DF.T_LIBGEN_r8) (t_st DF.R_LIBGEN_r8_RET).
Proof.
  intros HL HE. apply lib_ok_of. intros E0 K HPB HRET.
  exact (LN_T_LIBGEN_r8 R E0 K (Hyps R E0 K HPB HL HE HRET)).
Qed.
End LibRunSrc_r8.
