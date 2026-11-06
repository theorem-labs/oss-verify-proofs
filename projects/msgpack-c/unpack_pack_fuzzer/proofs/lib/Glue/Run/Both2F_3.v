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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Both2F Require Import T_Both2F B_00 B_01.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Both2F_1 Both2F_2.
Unset Nia Cache. Unset Nra Cache.

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

Definition SWC_T_SW_OPENERR__17 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__17) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__17 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__17) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__17) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__17 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__18 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__18) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__18 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__18) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__18) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__18 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__19 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__19) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__19 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__19) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__19) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__19 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__2 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__2) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__2 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__2) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__2) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__2 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__20 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__20) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__20 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__20) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__20) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__20 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__21 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__21) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__21 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__21) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__21) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__21 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__22 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__22) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__22 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__22) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__22) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__22 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__23 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__23) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__23 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__23) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__23) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__23 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__24 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__24) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__24 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__24) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__24) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__24 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__25 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__25) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63).
Lemma N_T_SW_OPENERR__25 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__25) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__25) (t_st T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63) SWC_T_SW_OPENERR__25 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c5f24_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60f5c8_w0_ev1_0x250bv1_0x250_q8e316_k63 R H)].
Qed.

