(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgAsan ItabAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanU Require UnivAsan.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.AsanNU Require Import T_AsanNU B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRVN 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import AsanNU_1 AsanNU_2 AsanNU_3.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_DRV_5 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_5) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_5 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_5) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_5) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_5 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_50 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_50) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_50 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_50) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_50) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_50 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_51 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_51) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_51 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_51) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_51) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_51 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_52 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_52) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_52 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_52) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_52) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_52 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_53 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_53) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_53 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_53) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_53) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_53 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_54 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_54) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_54 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_54) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_54) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_54 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_55 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_55) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_55 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_55) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_55) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_55 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_56 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_56) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_56 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_56) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_56) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_56 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_57 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_57) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_57 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_57) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_57) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_57 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_58 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_58) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_58 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_58) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_58) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_58 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_59 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_59) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_59 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_59) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_59) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_59 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_6 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_6) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_6 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_6) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_6) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_6 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_60 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_60) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_60 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_60) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_60) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_60 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_61 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_61) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_61 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_61) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_61) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_61 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_62 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_62) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_62 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_62) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_62) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_62 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

