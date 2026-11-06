(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2D Require Import T_Ubs2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Ubs2D_1 Ubs2D_2 Ubs2D_3.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

