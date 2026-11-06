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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2D Require Import T_Src2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Src2D_1 Src2D_2 Src2D_3 Src2D_4 Src2D_5 Src2D_6.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPENERR__29 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__29) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__29 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__29) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__29) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__29 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__3 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__3) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__3 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__3) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__3) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__3 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__30 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__30) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__30 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__30) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__30) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__30 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__31 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__31) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__31 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__31) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__31) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__31 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__32 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__32) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__32 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__32) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__32) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__32 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__33 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__33) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__33 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__33) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__33) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__33 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__34 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__34) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__34 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__34) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__34) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__34 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__35 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__35) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__35 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__35) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__35) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__35 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__36 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__36) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__36 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__36) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__36) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__36 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__37 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__37) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__37 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__37) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__37) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__37 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__38 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__38) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__38 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__38) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__38) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__38 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__39 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__39) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__39 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__39) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__39) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__39 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__4 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__4) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__4 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__4) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__4) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__4 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__40 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__40) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__40 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__40) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__40) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__40 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__41 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__41) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__41 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__41) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__41) (t_st T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__41 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4af94_r8o7n1o1n6o5n0o3n2_s67bd0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

