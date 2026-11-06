(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgBoth ItabBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr. Import Actr.TwinB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothU Require UnivBoth.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.BothNU Require Import T_BothNU B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRVN 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import BothNU_1.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_DRV_22 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_22) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_22 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_22) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_22) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_22 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_23 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_23) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_23 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_23) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_23) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_23 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_24 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_24) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_24 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_24) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_24) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_24 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_25 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_25) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_25 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_25) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_25) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_25 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_26 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_26) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_26 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_26) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_26) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_26 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_27 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_27) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_27 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_27) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_27) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_27 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_28 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_28) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_28 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_28) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_28) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_28 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_29 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_29) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_29 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_29) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_29) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_29 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_3 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_3) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_3 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_3) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_3) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_3 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_30 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_30) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_30 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_30) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_30) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_30 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_31 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_31) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_31 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_31) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_31) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_31 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_32 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_32) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_32 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_32) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_32) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_32 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_33 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_33) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_33 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_33) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_33) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_33 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_34 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_34) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_34 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_34) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_34) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_34 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

Definition SWC_T_SW_DRV_35 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_35) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6).
Lemma N_T_SW_DRV_35 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_35) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_35) (t_st T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6) SWC_T_SW_DRV_35 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q164c6 R H)].
Qed.

