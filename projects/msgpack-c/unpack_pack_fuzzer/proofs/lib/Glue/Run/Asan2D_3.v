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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2D_1 Asan2D_2.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPEN__0_36 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_36) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_36 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_36) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_36) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_36 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_37 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_37) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_37 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_37) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_37) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_37 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_38 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_38) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_38 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_38) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_38) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_38 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_39 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_39) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_39 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_39) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_39) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_39 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_4 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_4) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_4 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_4) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_4) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_4 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_40 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_40) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_40 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_40) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_40) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_40 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_41 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_41) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_41 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_41) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_41) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_41 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_42 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_42) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_42 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_42) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_42) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_42 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_43 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_43) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_43 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_43) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_43) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_43 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_44 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_44) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_44 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_44) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_44) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_44 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_45 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_45) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_45 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_45) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_45) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_45 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_46 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_46) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_46 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_46) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_46) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_46 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_47 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_47) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_47 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_47) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_47) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_47 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_48 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_48) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_48 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_48) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_48) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_48 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_49 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_49) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63).
Lemma N_T_SW_OPEN__0_49 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_49) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_49) (t_st T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63) SWC_T_SW_OPEN__0_49 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa84fa_k63 R H)].
Qed.

