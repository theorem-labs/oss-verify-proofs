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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Asan2T Require Import T_Asan2T B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2T_1 Asan2T_2 Asan2T_3 Asan2T_4.
Unset Nia Cache. Unset Nra Cache.

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
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.PLAN (t_st T_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.OBLS (DR R (SWr 2 [] (SX 2))) [(170%uint63, T_SW_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1)] [] C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX HC) C_SWRET_c3fb0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CHK).
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
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CTX C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.PLAN (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.OBLS (DR R (SX 2)) [] [(177%uint63, E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1)] C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CTX HC) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.CTX C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.PLAN (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka) C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.OBLS (DR R (SX 2)) [(175%uint63, T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka)] [] C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.CTX HC) C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka).
Lemma N_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka) SWC_T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1 2 [(CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_ka R H)].
Qed.

Lemma N_T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.PLAN (t_st T_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029) C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.OBLS (DR R (SWr 2 [(CLit NL)] (SX 2))) [(171%uint63, T_SW_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029_1)] [] C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CTX HC) C_SWRET_c49d0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd5b70_w0_ev1_0x250bv1_0x250_q7f029.CHK).
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
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_OPENERR_.CTX C_OPENERR_.PLAN (t_st T_OPENERR_) C_OPENERR_.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_SW_OPENERR__1); (102%uint63, T_SW_OPENERR__10); (103%uint63, T_SW_OPENERR__11); (104%uint63, T_SW_OPENERR__12); (105%uint63, T_SW_OPENERR__13); (106%uint63, T_SW_OPENERR__14); (107%uint63, T_SW_OPENERR__15); (108%uint63, T_SW_OPENERR__16); (109%uint63, T_SW_OPENERR__17); (110%uint63, T_SW_OPENERR__18); (111%uint63, T_SW_OPENERR__19); (112%uint63, T_SW_OPENERR__2); (113%uint63, T_SW_OPENERR__20); (114%uint63, T_SW_OPENERR__21); (115%uint63, T_SW_OPENERR__22); (116%uint63, T_SW_OPENERR__23); (117%uint63, T_SW_OPENERR__24); (118%uint63, T_SW_OPENERR__25); (119%uint63, T_SW_OPENERR__26); (120%uint63, T_SW_OPENERR__27); (121%uint63, T_SW_OPENERR__28); (122%uint63, T_SW_OPENERR__29); (123%uint63, T_SW_OPENERR__3); (124%uint63, T_SW_OPENERR__30); (125%uint63, T_SW_OPENERR__31); (126%uint63, T_SW_OPENERR__32); (127%uint63, T_SW_OPENERR__33); (128%uint63, T_SW_OPENERR__34); (129%uint63, T_SW_OPENERR__35); (130%uint63, T_SW_OPENERR__36); (131%uint63, T_SW_OPENERR__37); (132%uint63, T_SW_OPENERR__38); (133%uint63, T_SW_OPENERR__39); (134%uint63, T_SW_OPENERR__4); (135%uint63, T_SW_OPENERR__40); (136%uint63, T_SW_OPENERR__41); (137%uint63, T_SW_OPENERR__42); (138%uint63, T_SW_OPENERR__43); (139%uint63, T_SW_OPENERR__44); (140%uint63, T_SW_OPENERR__45); (141%uint63, T_SW_OPENERR__46); (142%uint63, T_SW_OPENERR__47); (143%uint63, T_SW_OPENERR__48); (144%uint63, T_SW_OPENERR__49); (145%uint63, T_SW_OPENERR__5); (146%uint63, T_SW_OPENERR__50); (147%uint63, T_SW_OPENERR__51); (148%uint63, T_SW_OPENERR__52); (149%uint63, T_SW_OPENERR__53); (150%uint63, T_SW_OPENERR__54); (151%uint63, T_SW_OPENERR__55); (152%uint63, T_SW_OPENERR__56); (153%uint63, T_SW_OPENERR__57); (154%uint63, T_SW_OPENERR__58); (155%uint63, T_SW_OPENERR__59); (156%uint63, T_SW_OPENERR__6); (157%uint63, T_SW_OPENERR__60); (158%uint63, T_SW_OPENERR__61); (159%uint63, T_SW_OPENERR__62); (160%uint63, T_SW_OPENERR__63); (161%uint63, T_SW_OPENERR__64); (162%uint63, T_SW_OPENERR__65); (163%uint63, T_SW_OPENERR__7); (164%uint63, T_SW_OPENERR__8); (165%uint63, T_SW_OPENERR__9)] [] C_OPENERR_.WF ITAB_ok (contracts_ok_of SEGS R C_OPENERR_.CTX HC) C_OPENERR_.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__1 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPENERR__10 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__11 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__12 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__13 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__14 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__15 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__16 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__17 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__18 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__19 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__2 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__20 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__21 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__22 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__23 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__24 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__25 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__26 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__27 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__28 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__29 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__3 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__30 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__31 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__32 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__33 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__34 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__35 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__36 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__37 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__38 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__39 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__4 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__40 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__41 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__42 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__43 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__44 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__45 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__46 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__47 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__48 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__49 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__5 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__50 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__51 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__52 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__53 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__54 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__55 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__56 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__57 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__58 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__59 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__6 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__60 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__61 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__62 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__63 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__64 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__65 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPENERR__7 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__8 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__9 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_DRV2 (R : drun) (H : hyps R) : NODE SEGS R T_DRV2 (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC.
  apply (node_cert SEGS R C_DRV.CTX C_DRV.PLAN T_DRV2 C_DRV.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(100%uint63, T_OPENERR_)] [] C_DRV.WF ITAB_ok (contracts_ok_of SEGS R C_DRV.CTX HC) C_DRV.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPENERR_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

