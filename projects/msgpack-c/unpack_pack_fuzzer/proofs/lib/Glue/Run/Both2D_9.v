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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Both2D_1 Both2D_2 Both2D_3 Both2D_4 Both2D_5 Both2D_6 Both2D_7 Both2D_8.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPENERR__58 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__58) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__58 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__58) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__58) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__58 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__59 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__59) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__59 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__59) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__59) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__59 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__6 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__6) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__6 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__6) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__6) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__6 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__60 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__60) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__60 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__60) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__60) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__60 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__61 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__61) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__61 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__61) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__61) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__61 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__62 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__62) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__62 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__62) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__62) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__62 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__63 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__63) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__63) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__63) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__63 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1) (DR R (SWr 2 [] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 2 [] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Lemma N_T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528) (DR R (SWr 2 [] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.CTX C_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.PLAN (t_st T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528) C_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.OBLS (DR R (SWr 2 [] (SX 2))) [(241%uint63, T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1)] [] C_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.CTX HC) C_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__64 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__64) (t_st T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528).
Lemma N_T_SW_OPENERR__64 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__64) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__64) (t_st T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528) SWC_T_SW_OPENERR__64 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c60f4_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 R H)].
Qed.

Lemma N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CTX C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.PLAN (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.OBLS (DR R (SX 2)) [] [(248%uint63, E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1)] C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CTX HC) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka.CTX C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka.PLAN (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka) C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka.OBLS (DR R (SX 2)) [(246%uint63, T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka)] [] C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka.CTX HC) C_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_ka R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka).
Lemma N_T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka) SWC_T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 2 [(CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_ka R H)].
Qed.

Lemma N_T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.CTX C_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.PLAN (t_st T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528) C_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.OBLS (DR R (SWr 2 [(CLit NL)] (SX 2))) [(242%uint63, T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1)] [] C_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.CTX HC) C_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__65 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__65) (t_st T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528).
Lemma N_T_SW_OPENERR__65 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__65) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__65) (t_st T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528) SWC_T_SW_OPENERR__65 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c6b14_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_sd7cb8_w0_ev1_0x250bv1_0x250_q57528 R H)].
Qed.

Definition SWC_T_SW_OPENERR__7 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__7) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__7 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__7) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__7) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__7 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__8 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__8) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__8 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__8) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__8) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__8 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__9 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__9) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__9 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__9) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__9) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__9 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Lemma N_T_OPENERR_ (R : drun) (H : hyps R) : NODE SEGS R (t_st T_OPENERR_) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_OPENERR_.CTX C_OPENERR_.PLAN (t_st T_OPENERR_) C_OPENERR_.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(169%uint63, T_SW_OPENERR__1); (170%uint63, T_SW_OPENERR__10); (171%uint63, T_SW_OPENERR__11); (172%uint63, T_SW_OPENERR__12); (173%uint63, T_SW_OPENERR__13); (174%uint63, T_SW_OPENERR__14); (175%uint63, T_SW_OPENERR__15); (176%uint63, T_SW_OPENERR__16); (177%uint63, T_SW_OPENERR__17); (178%uint63, T_SW_OPENERR__18); (179%uint63, T_SW_OPENERR__19); (180%uint63, T_SW_OPENERR__2); (181%uint63, T_SW_OPENERR__20); (182%uint63, T_SW_OPENERR__21); (183%uint63, T_SW_OPENERR__22); (184%uint63, T_SW_OPENERR__23); (185%uint63, T_SW_OPENERR__24); (186%uint63, T_SW_OPENERR__25); (187%uint63, T_SW_OPENERR__26); (188%uint63, T_SW_OPENERR__27); (189%uint63, T_SW_OPENERR__28); (190%uint63, T_SW_OPENERR__29); (191%uint63, T_SW_OPENERR__3); (192%uint63, T_SW_OPENERR__30); (193%uint63, T_SW_OPENERR__31); (194%uint63, T_SW_OPENERR__32); (195%uint63, T_SW_OPENERR__33); (196%uint63, T_SW_OPENERR__34); (197%uint63, T_SW_OPENERR__35); (198%uint63, T_SW_OPENERR__36); (199%uint63, T_SW_OPENERR__37); (200%uint63, T_SW_OPENERR__38); (201%uint63, T_SW_OPENERR__39); (202%uint63, T_SW_OPENERR__4); (203%uint63, T_SW_OPENERR__40); (204%uint63, T_SW_OPENERR__41); (205%uint63, T_SW_OPENERR__42); (206%uint63, T_SW_OPENERR__43); (207%uint63, T_SW_OPENERR__44); (208%uint63, T_SW_OPENERR__45); (209%uint63, T_SW_OPENERR__46); (210%uint63, T_SW_OPENERR__47); (211%uint63, T_SW_OPENERR__48); (212%uint63, T_SW_OPENERR__49); (213%uint63, T_SW_OPENERR__5); (214%uint63, T_SW_OPENERR__50); (215%uint63, T_SW_OPENERR__51); (216%uint63, T_SW_OPENERR__52); (217%uint63, T_SW_OPENERR__53); (218%uint63, T_SW_OPENERR__54); (219%uint63, T_SW_OPENERR__55); (220%uint63, T_SW_OPENERR__56); (221%uint63, T_SW_OPENERR__57); (222%uint63, T_SW_OPENERR__58); (223%uint63, T_SW_OPENERR__59); (224%uint63, T_SW_OPENERR__6); (225%uint63, T_SW_OPENERR__60); (226%uint63, T_SW_OPENERR__61); (227%uint63, T_SW_OPENERR__62); (228%uint63, T_SW_OPENERR__63); (229%uint63, T_SW_OPENERR__64); (230%uint63, T_SW_OPENERR__65); (231%uint63, T_SW_OPENERR__7); (232%uint63, T_SW_OPENERR__8); (233%uint63, T_SW_OPENERR__9)] [] C_OPENERR_.WF ITAB_ok (contracts_ok_of SEGS R C_OPENERR_.CTX HC) C_OPENERR_.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__1 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPENERR__10 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__11 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__12 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__13 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__14 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__15 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__16 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__17 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__18 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__19 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__2 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__20 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__21 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__22 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__23 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__24 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__25 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__26 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__27 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__28 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__29 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__3 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__30 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__31 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__32 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__33 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__34 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__35 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__36 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__37 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__38 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__39 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__4 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__40 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__41 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__42 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__43 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__44 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__45 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__46 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__47 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__48 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__49 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__5 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__50 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__51 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__52 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__53 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__54 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__55 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__56 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__57 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__58 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__59 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__6 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__60 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__61 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__62 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__63 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__64 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_OPEN_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_OPENERR__65 R H)])|]; apply Forall_cons; [exact (N_T_SW_OPENERR__7 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__8 R H)|]; apply Forall_cons; [exact (N_T_SW_OPENERR__9 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_OPEN__1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__1) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
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
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
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
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
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
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD.
  apply (node_cert SEGS R C_OPEN__4.CTX C_OPEN__4.PLAN (t_st R_OPEN__4) C_OPEN__4.OBLS (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_OPENERR_)] [] C_OPEN__4.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__4.CTX HC) C_OPEN__4.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_OPENERR_ R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

