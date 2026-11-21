(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/Run/SrcNU_3.v: the same certificate nodes of the usage path, over BudgetWit.DrvLibB.NODE_b *)

From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgSrc ItabSrc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.SrcNU Require Import T_SrcNU B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit Require Import Rzb PlanSoundB CertSoundB NodesB StdioWriteB DrvLibB.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Import PlanSB SWB DrvLibB.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRVN 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.Run Require Import SrcNUB_1 SrcNUB_2.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_DRV_36 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_36) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_36_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_36) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_36) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_36 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_37 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_37) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_37_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_37) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_37) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_37 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_38 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_38) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_38_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_38) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_38) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_38 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_39 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_39) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_39_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_39) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_39) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_39 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_4 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_4) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_4_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_4) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_4) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_4 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_40 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_40) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_40_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_40) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_40) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_40 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_41 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_41) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_41_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_41) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_41) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_41 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_42 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_42) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_42_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_42) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_42) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_42 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_43 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_43) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_43_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_43) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_43) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_43 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_44 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_44) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_44_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_44) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_44) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_44 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_45 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_45) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_45_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_45) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_45) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_45 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_46 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_46) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_46_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_46) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_46) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_46 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_47 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_47) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_47_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_47) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_47) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_47 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_48 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_48) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_48_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_48) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_48) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_48 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_49 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_49) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_49_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_49) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_49) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_49 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

