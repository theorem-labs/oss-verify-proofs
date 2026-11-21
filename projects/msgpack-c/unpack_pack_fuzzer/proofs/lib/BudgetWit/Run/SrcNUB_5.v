(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/Run/SrcNU_5.v: the same certificate nodes of the usage path, over BudgetWit.DrvLibB.NODE_b *)

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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.Run Require Import SrcNUB_1 SrcNUB_2 SrcNUB_3 SrcNUB_4.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_DRV_63 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_63) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_63_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_63) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_63) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_63 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_64 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_64) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_64_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_64) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_64) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_64 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_65 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_65) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_65_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_65) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_65) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_65 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_66 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_66) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_66_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_66) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_66) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_66 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_67 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_67) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_67_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_67) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_67) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_67 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (DR R (SWr 2 [] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 2 [] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Lemma N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) (DR R (SWr 2 [] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert_b SEGS R C_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CTX C_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.PLAN (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) C_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.OBLS (DR R (SWr 2 [] (SX 2))) [(179%uint63, T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)] [] C_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.WF ITAB_ok (contracts_ok_of_b SEGS R C_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CTX HC) C_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1_b R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_DRV_68 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_68) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_68_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_68) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_68) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_68 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_69 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_69) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_69_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_69) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_69) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_69 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_7 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_7) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_7_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_7) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_7) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_7 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_70 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_70) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_70_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_70) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_70) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_70 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_71 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_71) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_71_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_71) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_71) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_71 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_72 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_72) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_72_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_72) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_72) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_72 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_73 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_73) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_73_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_73) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_73) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_73 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_74 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_74) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_74_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_74) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_74) (t_st T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_74 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4b164_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

