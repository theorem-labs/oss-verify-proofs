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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2D Require Import T_Both2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

Record hyps (R : drun) : Prop := Hyps {
  h_ctab : ctab_ok SEGS R T_Both2D.CONTRACTS;
  h_famd : path_is_dirref (r_p1 R) = true
}.

Lemma N_E_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN (t_st T_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) C_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS (DR R (SX 2)) [] [(239%uint63, E_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1)] C_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) C_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d.CTX C_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d.PLAN (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) C_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d.OBLS (DR R (SX 2)) [(168%uint63, T_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d.CTX HC) C_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPEN__0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_1) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_1) (DR R (SWr 2 [(CLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 10])] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_1) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_1 2 [(CLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 10])] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_10 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_10) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_10 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_10) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_10) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_10 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_11 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_11) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_11 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_11) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_11) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_11 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_12 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_12) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_12 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_12) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_12) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_12 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_13 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_13) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_13 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_13) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_13) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_13 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_14 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_14) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_14 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_14) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_14) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_14 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_15 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_15) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_15 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_15) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_15) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_15 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_16 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_16) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_16 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_16) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_16) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_16 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_17 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_17) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_17 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_17) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_17) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_17 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_18 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_18) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_18 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_18) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_18) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_18 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_19 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_19) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_19 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_19) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_19) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_19 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_2 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_2) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_2 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_2) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_2) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_2 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_20 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_20) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_20 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_20) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_20) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_20 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_21 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_21) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_21 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_21) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_21) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_21 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

