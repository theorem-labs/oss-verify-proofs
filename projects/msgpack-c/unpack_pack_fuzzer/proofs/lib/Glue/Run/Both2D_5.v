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
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Both2D_1 Both2D_2 Both2D_3 Both2D_4.
Unset Nia Cache. Unset Nra Cache.

Lemma N_T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557) (DR R (SWr 2 [] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.CTX C_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.PLAN (t_st T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557) C_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.OBLS (DR R (SWr 2 [] (SX 2))) [(234%uint63, T_SW_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1)] [] C_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.CTX HC) C_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPEN__0_62 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_62) (t_st T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557).
Lemma N_T_SW_OPEN__0_62 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_62) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_62) (t_st T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557) SWC_T_SW_OPEN__0_62 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c60f4_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557 R H)].
Qed.

Definition SWC_T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 2 [(CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Lemma N_T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.CTX C_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.PLAN (t_st T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557) C_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.OBLS (DR R (SWr 2 [(CLit NL)] (SX 2))) [(235%uint63, T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1)] [] C_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.CTX HC) C_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPEN__0_63 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_63) (t_st T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557).
Lemma N_T_SW_OPEN__0_63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_63) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_63) (t_st T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557) SWC_T_SW_OPEN__0_63 2 [(CLit MSG_RDERR_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c6b14_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q79557 R H)].
Qed.

Definition SWC_T_SW_OPEN__0_7 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_7) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_7 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_7) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_7) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_7 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_8 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_8) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_8 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_8) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_8) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_8 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Definition SWC_T_SW_OPEN__0_9 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPEN__0_9) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d).
Lemma N_T_SW_OPEN__0_9 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPEN__0_9) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPEN__0_9) (t_st T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d) SWC_T_SW_OPEN__0_9 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r10o4n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_qa851d R H)].
Qed.

Lemma N_R_OPEN__0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__0) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_OPEN__0.CTX C_OPEN__0.PLAN (t_st R_OPEN__0) C_OPEN__0.OBLS (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))) [(102%uint63, T_SW_OPEN__0_1); (103%uint63, T_SW_OPEN__0_10); (104%uint63, T_SW_OPEN__0_11); (105%uint63, T_SW_OPEN__0_12); (106%uint63, T_SW_OPEN__0_13); (107%uint63, T_SW_OPEN__0_14); (108%uint63, T_SW_OPEN__0_15); (109%uint63, T_SW_OPEN__0_16); (110%uint63, T_SW_OPEN__0_17); (111%uint63, T_SW_OPEN__0_18); (112%uint63, T_SW_OPEN__0_19); (113%uint63, T_SW_OPEN__0_2); (114%uint63, T_SW_OPEN__0_20); (115%uint63, T_SW_OPEN__0_21); (116%uint63, T_SW_OPEN__0_22); (117%uint63, T_SW_OPEN__0_23); (118%uint63, T_SW_OPEN__0_24); (119%uint63, T_SW_OPEN__0_25); (120%uint63, T_SW_OPEN__0_26); (121%uint63, T_SW_OPEN__0_27); (122%uint63, T_SW_OPEN__0_28); (123%uint63, T_SW_OPEN__0_29); (124%uint63, T_SW_OPEN__0_3); (125%uint63, T_SW_OPEN__0_30); (126%uint63, T_SW_OPEN__0_31); (127%uint63, T_SW_OPEN__0_32); (128%uint63, T_SW_OPEN__0_33); (129%uint63, T_SW_OPEN__0_34); (130%uint63, T_SW_OPEN__0_35); (131%uint63, T_SW_OPEN__0_36); (132%uint63, T_SW_OPEN__0_37); (133%uint63, T_SW_OPEN__0_38); (134%uint63, T_SW_OPEN__0_39); (135%uint63, T_SW_OPEN__0_4); (136%uint63, T_SW_OPEN__0_40); (137%uint63, T_SW_OPEN__0_41); (138%uint63, T_SW_OPEN__0_42); (139%uint63, T_SW_OPEN__0_43); (140%uint63, T_SW_OPEN__0_44); (141%uint63, T_SW_OPEN__0_45); (142%uint63, T_SW_OPEN__0_46); (143%uint63, T_SW_OPEN__0_47); (144%uint63, T_SW_OPEN__0_48); (145%uint63, T_SW_OPEN__0_49); (146%uint63, T_SW_OPEN__0_5); (147%uint63, T_SW_OPEN__0_50); (148%uint63, T_SW_OPEN__0_51); (149%uint63, T_SW_OPEN__0_52); (150%uint63, T_SW_OPEN__0_53); (151%uint63, T_SW_OPEN__0_54); (152%uint63, T_SW_OPEN__0_55); (153%uint63, T_SW_OPEN__0_56); (154%uint63, T_SW_OPEN__0_57); (155%uint63, T_SW_OPEN__0_58); (156%uint63, T_SW_OPEN__0_59); (157%uint63, T_SW_OPEN__0_6); (158%uint63, T_SW_OPEN__0_60); (159%uint63, T_SW_OPEN__0_61); (160%uint63, T_SW_OPEN__0_62); (161%uint63, T_SW_OPEN__0_63); (162%uint63, T_SW_OPEN__0_7); (163%uint63, T_SW_OPEN__0_8); (164%uint63, T_SW_OPEN__0_9)] [] C_OPEN__0.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__0.CTX HC) C_OPEN__0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_OPEN__0_1 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_10 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_11 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_12 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_13 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_14 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_15 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_16 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_17 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_18 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_19 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_2 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_20 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_21 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_22 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_23 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_24 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_25 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_26 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_27 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_28 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_29 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_3 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_30 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_31 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_32 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_33 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_34 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_35 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_36 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_37 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_38 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_39 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_4 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_40 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_41 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_42 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_43 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_44 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_45 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_46 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_47 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_48 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_49 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_5 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_50 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_51 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_52 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_53 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_54 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_55 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_56 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_57 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_58 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_59 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_6 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_60 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_61 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPEN__0_62 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_RDERR_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPEN__0_63 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_7 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_8 R H)|]; apply Forall_cons; [exact (N_T_SW_OPEN__0_9 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.CTX C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.PLAN (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.OBLS (DR R (SX 2)) [] [(247%uint63, E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1)] C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.CTX HC) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63.CTX C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63.PLAN (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63.OBLS (DR R (SX 2)) [(245%uint63, T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63)] [] C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63.CTX HC) C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__1) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__1) (DR R (SWr 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__1) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__1 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__10 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__10) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__10 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__10) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__10) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__10 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__11 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__11) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__11 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__11) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__11) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__11 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__12 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__12) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__12 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__12) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__12) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__12 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__13 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__13) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__13 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__13) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__13) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__13 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__14 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__14) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__14 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__14) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__14) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__14 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__15 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__15) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__15 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__15) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__15) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__15 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__16 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__16) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__16 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__16) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__16) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__16 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

