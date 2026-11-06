(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRVN 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import SrcNU_1 SrcNU_2 SrcNU_3 SrcNU_4 SrcNU_5.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (DR R (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 2 [(CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230 R H)].
Qed.

Lemma N_T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) (DR R (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CTX C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.PLAN (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.OBLS (DR R (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))) [(180%uint63, T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1)] [] C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CTX HC) C_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_DRV_75 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_75) (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_75 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_75) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0] (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_75) (t_st T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_75 2 [(CLit MSG_USAGE_PRE); CA0] (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4bb84_r7o7n1o1n6o5n0o3n2_s566c8_w0_ev1_0x230bv1_0x230 R H)].
Qed.

Definition SWC_T_SW_DRV_8 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_8) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_8 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_8) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_8) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_8 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230 R H)].
Qed.

Definition SWC_T_SW_DRV_9 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_DRV_9) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_DRV_9 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_DRV_9) (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_DRV_9) (t_st T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230) SWC_T_SW_DRV_9 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r7o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230 R H)].
Qed.

Lemma N_T_DRVN (R : drun) (H : hyps R) : NODE SEGS R T_DRVN (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_DRV.CTX C_DRV.PLAN T_DRVN C_DRV.OBLS (DR R (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SX 2))) [(100%uint63, T_SW_DRV_1); (101%uint63, T_SW_DRV_10); (102%uint63, T_SW_DRV_11); (103%uint63, T_SW_DRV_12); (104%uint63, T_SW_DRV_13); (105%uint63, T_SW_DRV_14); (106%uint63, T_SW_DRV_15); (107%uint63, T_SW_DRV_16); (108%uint63, T_SW_DRV_17); (109%uint63, T_SW_DRV_18); (110%uint63, T_SW_DRV_19); (111%uint63, T_SW_DRV_2); (112%uint63, T_SW_DRV_20); (113%uint63, T_SW_DRV_21); (114%uint63, T_SW_DRV_22); (115%uint63, T_SW_DRV_23); (116%uint63, T_SW_DRV_24); (117%uint63, T_SW_DRV_25); (118%uint63, T_SW_DRV_26); (119%uint63, T_SW_DRV_27); (120%uint63, T_SW_DRV_28); (121%uint63, T_SW_DRV_29); (122%uint63, T_SW_DRV_3); (123%uint63, T_SW_DRV_30); (124%uint63, T_SW_DRV_31); (125%uint63, T_SW_DRV_32); (126%uint63, T_SW_DRV_33); (127%uint63, T_SW_DRV_34); (128%uint63, T_SW_DRV_35); (129%uint63, T_SW_DRV_36); (130%uint63, T_SW_DRV_37); (131%uint63, T_SW_DRV_38); (132%uint63, T_SW_DRV_39); (133%uint63, T_SW_DRV_4); (134%uint63, T_SW_DRV_40); (135%uint63, T_SW_DRV_41); (136%uint63, T_SW_DRV_42); (137%uint63, T_SW_DRV_43); (138%uint63, T_SW_DRV_44); (139%uint63, T_SW_DRV_45); (140%uint63, T_SW_DRV_46); (141%uint63, T_SW_DRV_47); (142%uint63, T_SW_DRV_48); (143%uint63, T_SW_DRV_49); (144%uint63, T_SW_DRV_5); (145%uint63, T_SW_DRV_50); (146%uint63, T_SW_DRV_51); (147%uint63, T_SW_DRV_52); (148%uint63, T_SW_DRV_53); (149%uint63, T_SW_DRV_54); (150%uint63, T_SW_DRV_55); (151%uint63, T_SW_DRV_56); (152%uint63, T_SW_DRV_57); (153%uint63, T_SW_DRV_58); (154%uint63, T_SW_DRV_59); (155%uint63, T_SW_DRV_6); (156%uint63, T_SW_DRV_60); (157%uint63, T_SW_DRV_61); (158%uint63, T_SW_DRV_62); (159%uint63, T_SW_DRV_63); (160%uint63, T_SW_DRV_64); (161%uint63, T_SW_DRV_65); (162%uint63, T_SW_DRV_66); (163%uint63, T_SW_DRV_67); (164%uint63, T_SW_DRV_68); (165%uint63, T_SW_DRV_69); (166%uint63, T_SW_DRV_7); (167%uint63, T_SW_DRV_70); (168%uint63, T_SW_DRV_71); (169%uint63, T_SW_DRV_72); (170%uint63, T_SW_DRV_73); (171%uint63, T_SW_DRV_74); (172%uint63, T_SW_DRV_75); (173%uint63, T_SW_DRV_8); (174%uint63, T_SW_DRV_9)] [] C_DRV.WF ITAB_ok (contracts_ok_of SEGS R C_DRV.CTX HC) C_DRV.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_DRV_1 R H)])|]; apply Forall_cons; [exact (N_T_SW_DRV_10 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_11 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_12 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_13 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_14 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_15 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_16 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_17 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_18 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_19 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_2 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_20 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_21 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_22 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_23 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_24 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_25 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_26 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_27 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_28 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_29 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_3 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_30 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_31 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_32 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_33 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_34 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_35 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_36 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_37 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_38 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_39 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_4 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_40 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_41 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_42 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_43 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_44 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_45 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_46 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_47 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_48 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_49 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_5 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_50 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_51 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_52 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_53 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_54 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_55 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_56 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_57 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_58 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_59 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_6 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_60 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_61 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_62 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_63 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_64 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_65 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_66 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_67 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_68 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_69 R H)])|]; apply Forall_cons; [exact (N_T_SW_DRV_7 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_70 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_71 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_72 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_73 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0; (CLit MSG_USAGE_POST)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_74 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_USAGE_PRE); CA0] (SWr 2 [(CLit MSG_USAGE_POST)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_DRV_75 R H)])|]; apply Forall_cons; [exact (N_T_SW_DRV_8 R H)|]; apply Forall_cons; [exact (N_T_SW_DRV_9 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

