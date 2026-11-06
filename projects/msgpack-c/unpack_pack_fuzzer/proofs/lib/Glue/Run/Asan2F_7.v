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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2F_1 Asan2F_2 Asan2F_3 Asan2F_4 Asan2F_5 Asan2F_6.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka).
Lemma N_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka) SWC_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 2 [(CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka R H)].
Qed.

Lemma N_T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.PLAN (t_st T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.OBLS (DR R (SWr 2 [(CLit NL)] (SX 2))) [(209%uint63, T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1)] [] C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX HC) C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__65 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__65) (t_st T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029).
Lemma N_T_SW_OPENERR__65 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__65) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__65) (t_st T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) SWC_T_SW_OPENERR__65 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029 R H)].
Qed.

Definition SWC_T_SW_OPENERR__7 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__7) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__7 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__7) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__7) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__7 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__8 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__8) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__8 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__8) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__8) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__8 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__9 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__9) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__9 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__9) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__9) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__9 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Lemma N_T_OPENERR_ (R : drun) (H : hyps R) : NODE SEGS R (t_st T_OPENERR_) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_OPENERR_.CTX C_OPENERR_.PLAN (t_st T_OPENERR_) C_OPENERR_.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(117%uint63, T_SW_OPENERR__1); (118%uint63, T_SW_OPENERR__10); (119%uint63, T_SW_OPENERR__11); (120%uint63, T_SW_OPENERR__12); (121%uint63, T_SW_OPENERR__13); (122%uint63, T_SW_OPENERR__14); (123%uint63, T_SW_OPENERR__15); (124%uint63, T_SW_OPENERR__16); (125%uint63, T_SW_OPENERR__17); (126%uint63, T_SW_OPENERR__18); (127%uint63, T_SW_OPENERR__19); (128%uint63, T_SW_OPENERR__2); (129%uint63, T_SW_OPENERR__20); (130%uint63, T_SW_OPENERR__21); (131%uint63, T_SW_OPENERR__22); (132%uint63, T_SW_OPENERR__23); (133%uint63, T_SW_OPENERR__24); (134%uint63, T_SW_OPENERR__25); (135%uint63, T_SW_OPENERR__26); (136%uint63, T_SW_OPENERR__27); (137%uint63, T_SW_OPENERR__28); (138%uint63, T_SW_OPENERR__29); (139%uint63, T_SW_OPENERR__3); (140%uint63, T_SW_OPENERR__30); (141%uint63, T_SW_OPENERR__31); (142%uint63, T_SW_OPENERR__32); (143%uint63, T_SW_OPENERR__33); (144%uint63, T_SW_OPENERR__34); (145%uint63, T_SW_OPENERR__35); (146%uint63, T_SW_OPENERR__36); (147%uint63, T_SW_OPENERR__37); (148%uint63, T_SW_OPENERR__38); (149%uint63, T_SW_OPENERR__39); (150%uint63, T_SW_OPENERR__4); (151%uint63, T_SW_OPENERR__40); (152%uint63, T_SW_OPENERR__41); (153%uint63, T_SW_OPENERR__42); (154%uint63, T_SW_OPENERR__43); (155%uint63, T_SW_OPENERR__44); (156%uint63, T_SW_OPENERR__45); (157%uint63, T_SW_OPENERR__46); (158%uint63, T_SW_OPENERR__47); (159%uint63, T_SW_OPENERR__48); (160%uint63, T_SW_OPENERR__49); (161%uint63, T_SW_OPENERR__5); (162%uint63, T_SW_OPENERR__50); (163%uint63, T_SW_OPENERR__51); (164%uint63, T_SW_OPENERR__52); (165%uint63, T_SW_OPENERR__53); (166%uint63, T_SW_OPENERR__54); (167%uint63, T_SW_OPENERR__55); (168%uint63, T_SW_OPENERR__56); (169%uint63, T_SW_OPENERR__57); (170%uint63, T_SW_OPENERR__58); (171%uint63, T_SW_OPENERR__59); (172%uint63, T_SW_OPENERR__6); (173%uint63, T_SW_OPENERR__60); (174%uint63, T_SW_OPENERR__61); (175%uint63, T_SW_OPENERR__62); (176%uint63, T_SW_OPENERR__63); (177%uint63, T_SW_OPENERR__64); (178%uint63, T_SW_OPENERR__65); (179%uint63, T_SW_OPENERR__7); (180%uint63, T_SW_OPENERR__8); (181%uint63, T_SW_OPENERR__9)] [] C_OPENERR_.WF ITAB_ok (contracts_ok_of SEGS R C_OPENERR_.CTX HC) C_OPENERR_.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__1 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPENERR__10 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__11 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__12 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__13 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__14 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__15 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__16 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__17 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__18 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__19 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__2 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__20 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__21 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__22 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__23 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__24 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__25 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__26 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__27 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__28 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__29 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__3 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__30 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__31 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__32 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__33 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__34 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__35 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__36 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__37 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__38 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__39 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__4 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__40 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__41 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__42 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__43 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__44 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__45 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__46 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__47 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__48 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__49 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__5 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__50 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__51 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__52 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__53 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__54 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__55 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__56 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__57 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__58 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__59 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__6 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__60 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__61 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__62 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__63 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__64 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__65 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPENERR__7 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__8 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__9 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_OPEN__1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__1) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_OPEN__1.CTX C_OPEN__1.PLAN (t_st R_OPEN__1) C_OPEN__1.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_OPENERR_)] [] C_OPEN__1.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__1.CTX HC) C_OPEN__1.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPENERR_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_OPEN__2 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__2) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_OPEN__2.CTX C_OPEN__2.PLAN (t_st R_OPEN__2) C_OPEN__2.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_OPENERR_)] [] C_OPEN__2.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__2.CTX HC) C_OPEN__2.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPENERR_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_OPEN__3 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__3) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_OPEN__3.CTX C_OPEN__3.PLAN (t_st R_OPEN__3) C_OPEN__3.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_OPENERR_)] [] C_OPEN__3.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__3.CTX HC) C_OPEN__3.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPENERR_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_OPEN__4 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__4) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_OPEN__4.CTX C_OPEN__4.PLAN (t_st R_OPEN__4) C_OPEN__4.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_OPENERR_)] [] C_OPEN__4.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__4.CTX HC) C_OPEN__4.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPENERR_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_OPEN_ (R : drun) (H : hyps R) : NODE SEGS R (t_st T_OPEN_) (DR R (SALT (RDn (r_file R) 10 65536) (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_open_file SEGS R MPF FAMF (t_st T_OPEN_) _ (DR R (RDn (r_file R) 10 65536)) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) T_Asan2F.FORK_OPEN_ ltac:(vm_compute; reflexivity)).
  - exact (N_R_OPEN__0 R H).
  - apply Forall_cons; [exact (N_R_OPEN__1 R H)|]; apply Forall_cons; [exact (N_R_OPEN__2 R H)|]; apply Forall_cons; [exact (N_R_OPEN__3 R H)|]; apply Forall_cons; [exact (N_R_OPEN__4 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_DRV2 (R : drun) (H : hyps R) : NODE SEGS R T_DRV2 (DR R (SALT (RDn (r_file R) 10 65536) (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_DRV.CTX C_DRV.PLAN T_DRV2 C_DRV.OBLS (DR R (SALT (RDn (r_file R) 10 65536) (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)))) [(100%uint63, T_OPEN_)] [] C_DRV.WF ITAB_ok (contracts_ok_of SEGS R C_DRV.CTX HC) C_DRV.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPEN_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

