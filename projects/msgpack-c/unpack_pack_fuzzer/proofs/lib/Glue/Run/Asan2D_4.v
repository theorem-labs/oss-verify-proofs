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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2D_1 Asan2D_2 Asan2D_3.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPEN__0_5 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_5) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_5 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_5) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_5) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_5 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_50 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_50) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_50 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_50) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_50) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_50 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_51 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_51) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_51 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_51) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_51) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_51 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_52 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_52) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_52 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_52) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_52) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_52 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_53 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_53) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_53 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_53) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_53) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_53 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_54 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_54) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_54 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_54) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_54) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_54 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_55 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_55) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_55 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_55) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_55) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_55 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_56 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_56) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_56 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_56) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_56) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_56 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_57 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_57) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_57 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_57) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_57) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_57 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_58 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_58) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_58 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_58) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_58) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_58 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_59 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_59) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_59 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_59) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_59) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_59 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_6 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_6) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_6 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_6) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_6) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_6 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_60 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_60) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_60 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_60) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_60) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_60 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_61 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_61) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_61 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_61) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_61) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_61 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_SWRET_c3fb0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qa1c4c_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c3fb0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qa1c4c_1) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_SWRET_c3fb0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qa1c4c_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c3fb0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qa1c4c_1) (DR R (SWr 2 [] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c3fb0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qa1c4c_1) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_SWRET_c3fb0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qa1c4c_1 2 [] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

