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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import AsanNU_1 AsanNU_2 AsanNU_3 AsanNU_4.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_DRV_63 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_63) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_63) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_63) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_63 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_64 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_64) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_64 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_64) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_64) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_64 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_65 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_65) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_65 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_65) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_65) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_65 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_66 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_66) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_66 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_66) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_66) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_66 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_67 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_67) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_67 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_67) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_67) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_67 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1) (DR R (SWr 2 [] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1 2 [] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Lemma N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) (DR R (SWr 2 [] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201.CTX C_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201.PLAN (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) C_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201.OBLS (DR R (SWr 2 [] (SX 2))) [(179%uint63, T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1)] [] C_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201.CTX HC) C_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_DRV_68 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_68) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_68 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_68) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_68) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_68 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

Definition SWC_T_SW_DRV_69 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_69) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_69 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_69) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_69) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_69 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

Definition SWC_T_SW_DRV_7 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_7) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76).
Lemma N_T_SW_DRV_7 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_7) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_7) (t_st T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76) SWC_T_SW_DRV_7 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_qa8b76 R H)].
Qed.

Definition SWC_T_SW_DRV_70 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_70) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_70 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_70) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_70) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_70 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

Definition SWC_T_SW_DRV_71 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_71) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_71 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_71) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_71) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_71 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

Definition SWC_T_SW_DRV_72 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_72) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_72 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_72) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_72) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_72 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

Definition SWC_T_SW_DRV_73 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_73) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_73 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_73) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_73) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_73 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

Definition SWC_T_SW_DRV_74 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_74) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201).
Lemma N_T_SW_DRV_74 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_74) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_74) (t_st T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201) SWC_T_SW_DRV_74 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3fb0_r7o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_qe4201 R H)].
Qed.

