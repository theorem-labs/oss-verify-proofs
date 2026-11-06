(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2D Require Import T_Src2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Src2D_1.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

