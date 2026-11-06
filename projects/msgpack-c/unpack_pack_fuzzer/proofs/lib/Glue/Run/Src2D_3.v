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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Src2D_1 Src2D_2.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48) (t_st T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1edd4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r9o4n0o7n1o1n9o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

