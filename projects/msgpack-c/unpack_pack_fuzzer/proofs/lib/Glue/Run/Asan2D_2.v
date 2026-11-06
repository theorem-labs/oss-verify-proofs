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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2D Require Import T_Asan2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2D_1.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPEN__0_22 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_22) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_22 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_22) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_22) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_22 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_23 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_23) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_23 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_23) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_23) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_23 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_24 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_24) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_24 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_24) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_24) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_24 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_25 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_25) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_25 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_25) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_25) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_25 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_26 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_26) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_26 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_26) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_26) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_26 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_27 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_27) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_27 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_27) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_27) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_27 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_28 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_28) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_28 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_28) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_28) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_28 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_29 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_29) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_29 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_29) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_29) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_29 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_3 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_3) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_3 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_3) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_3) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_3 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_30 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_30) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_30 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_30) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_30) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_30 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_31 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_31) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_31 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_31) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_31) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_31 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_32 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_32) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_32 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_32) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_32) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_32 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_33 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_33) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_33 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_33) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_33) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_33 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_34 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_34) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_34 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_34) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_34) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_34 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_35 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_35) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_35 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_35) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_35) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_35 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

