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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2F Require Import T_Asan2F B_00 B_01.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2F_1 Asan2F_2 Asan2F_3 Asan2F_4 Asan2F_5.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPENERR__53 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__53) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__53 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__53) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__53) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__53 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__54 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__54) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__54 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__54) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__54) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__54 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__55 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__55) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__55 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__55) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__55) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__55 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__56 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__56) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__56 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__56) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__56) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__56 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__57 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__57) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__57 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__57) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__57) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__57 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__58 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__58) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__58 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__58) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__58) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__58 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__59 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__59) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__59 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__59) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__59) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__59 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__6 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__6) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__6 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__6) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__6) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__6 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__60 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__60) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__60 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__60) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__60) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__60 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__61 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__61) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__61 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__61) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__61) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__61 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__62 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__62) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__62 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__62) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__62) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__62 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__63 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__63) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__63) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__63) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__63 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (DR R (SWr 2 [] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 2 [] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Lemma N_T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) (DR R (SWr 2 [] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.PLAN (t_st T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.OBLS (DR R (SWr 2 [] (SX 2))) [(208%uint63, T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1)] [] C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX HC) C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__64 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__64) (t_st T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029).
Lemma N_T_SW_OPENERR__64 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__64) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__64) (t_st T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) SWC_T_SW_OPENERR__64 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029 R H)].
Qed.

Lemma N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CTX C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.PLAN (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.OBLS (DR R (SX 2)) [] [(234%uint63, E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1)] C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CTX HC) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.CTX C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.PLAN (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka) C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.OBLS (DR R (SX 2)) [(231%uint63, T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka)] [] C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.CTX HC) C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

