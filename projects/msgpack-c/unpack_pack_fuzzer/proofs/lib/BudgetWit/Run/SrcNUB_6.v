(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from Glue/Run/SrcNU_6.v: the same certificate nodes of the usage path, over BudgetWit.DrvLibB.NODE_b *)

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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BudgetWit.Run Require Import SrcNUB_1 SrcNUB_2 SrcNUB_3 SrcNUB_4 SrcNUB_5.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (DR R (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 2 [(CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Lemma N_T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) (DR R (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert_b SEGS R C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CTX C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.PLAN (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.OBLS (DR R (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))) [(180%uint63, T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)] [] C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.WF ITAB_ok (contracts_ok_of_b SEGS R C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CTX HC) C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1_b R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_DRV_75 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_75) (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_75_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_75) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0] (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2)))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_75) (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_75 2 [(CLit MSG_USAGE_PRE); CA0] (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_8 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_8) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_8_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_8) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_8) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_8 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Definition SWC_T_SW_DRV_9 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_9) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_9_b (R : drun) (H : hyps_b R) : NODE_b SEGS R (t_st T_SW_DRV_9) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_9) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_9 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_b R H)].
Qed.

Lemma N_T_DRVN_b (R : drun) (H : hyps_b R) : NODE_b SEGS R T_DRVN (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert_b SEGS R C_DRV.CTX C_DRV.PLAN T_DRVN C_DRV.OBLS (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))) [(100%uint63, T_SW_DRV_1); (101%uint63, T_SW_DRV_10); (102%uint63, T_SW_DRV_11); (103%uint63, T_SW_DRV_12); (104%uint63, T_SW_DRV_13); (105%uint63, T_SW_DRV_14); (106%uint63, T_SW_DRV_15); (107%uint63, T_SW_DRV_16); (108%uint63, T_SW_DRV_17); (109%uint63, T_SW_DRV_18); (110%uint63, T_SW_DRV_19); (111%uint63, T_SW_DRV_2); (112%uint63, T_SW_DRV_20); (113%uint63, T_SW_DRV_21); (114%uint63, T_SW_DRV_22); (115%uint63, T_SW_DRV_23); (116%uint63, T_SW_DRV_24); (117%uint63, T_SW_DRV_25); (118%uint63, T_SW_DRV_26); (119%uint63, T_SW_DRV_27); (120%uint63, T_SW_DRV_28); (121%uint63, T_SW_DRV_29); (122%uint63, T_SW_DRV_3); (123%uint63, T_SW_DRV_30); (124%uint63, T_SW_DRV_31); (125%uint63, T_SW_DRV_32); (126%uint63, T_SW_DRV_33); (127%uint63, T_SW_DRV_34); (128%uint63, T_SW_DRV_35); (129%uint63, T_SW_DRV_36); (130%uint63, T_SW_DRV_37); (131%uint63, T_SW_DRV_38); (132%uint63, T_SW_DRV_39); (133%uint63, T_SW_DRV_4); (134%uint63, T_SW_DRV_40); (135%uint63, T_SW_DRV_41); (136%uint63, T_SW_DRV_42); (137%uint63, T_SW_DRV_43); (138%uint63, T_SW_DRV_44); (139%uint63, T_SW_DRV_45); (140%uint63, T_SW_DRV_46); (141%uint63, T_SW_DRV_47); (142%uint63, T_SW_DRV_48); (143%uint63, T_SW_DRV_49); (144%uint63, T_SW_DRV_5); (145%uint63, T_SW_DRV_50); (146%uint63, T_SW_DRV_51); (147%uint63, T_SW_DRV_52); (148%uint63, T_SW_DRV_53); (149%uint63, T_SW_DRV_54); (150%uint63, T_SW_DRV_55); (151%uint63, T_SW_DRV_56); (152%uint63, T_SW_DRV_57); (153%uint63, T_SW_DRV_58); (154%uint63, T_SW_DRV_59); (155%uint63, T_SW_DRV_6); (156%uint63, T_SW_DRV_60); (157%uint63, T_SW_DRV_61); (158%uint63, T_SW_DRV_62); (159%uint63, T_SW_DRV_63); (160%uint63, T_SW_DRV_64); (161%uint63, T_SW_DRV_65); (162%uint63, T_SW_DRV_66); (163%uint63, T_SW_DRV_67); (164%uint63, T_SW_DRV_68); (165%uint63, T_SW_DRV_69); (166%uint63, T_SW_DRV_7); (167%uint63, T_SW_DRV_70); (168%uint63, T_SW_DRV_71); (169%uint63, T_SW_DRV_72); (170%uint63, T_SW_DRV_73); (171%uint63, T_SW_DRV_74); (172%uint63, T_SW_DRV_75); (173%uint63, T_SW_DRV_8); (174%uint63, T_SW_DRV_9)] [] C_DRV.WF ITAB_ok (contracts_ok_of_b SEGS R C_DRV.CTX HC) C_DRV.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_DRV_1_b R H)])|]; apply Forall_cons; [exact (N_T_SW_DRV_10_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_11_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_12_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_13_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_14_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_15_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_16_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_17_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_18_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_19_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_2_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_20_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_21_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_22_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_23_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_24_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_25_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_26_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_27_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_28_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_29_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_3_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_30_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_31_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_32_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_33_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_34_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_35_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_36_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_37_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_38_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_39_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_4_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_40_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_41_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_42_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_43_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_44_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_45_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_46_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_47_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_48_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_49_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_5_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_50_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_51_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_52_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_53_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_54_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_55_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_56_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_57_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_58_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_59_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_6_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_60_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_61_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_62_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_63_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_64_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_65_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_66_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_67_b R H)|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_68_b R H)])|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_69_b R H)])|]; apply Forall_cons; [exact (N_T_SW_DRV_7_b R H)|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_70_b R H)])|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_71_b R H)])|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_72_b R H)])|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_73_b R H)])|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_74_b R H)])|]; apply Forall_cons; [(apply (node_eqv_f_b SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0] (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_75_b R H)])|]; apply Forall_cons; [exact (N_T_SW_DRV_8_b R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_9_b R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

