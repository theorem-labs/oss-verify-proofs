(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr State Step Plan Notation PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2T Require Import T_Ubs2T B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Ubs2T_1 Ubs2T_2 Ubs2T_3.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_OPENERR__5 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__5) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__5 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__5) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__5) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__5 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__50 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__50) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__50 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__50) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__50) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__50 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__51 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__51) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__51 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__51) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__51) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__51 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__52 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__52) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__52 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__52) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__52) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__52 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__53 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__53) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__53 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__53) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__53) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__53 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__54 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__54) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__54 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__54) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__54) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__54 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__55 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__55) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__55 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__55) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__55) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__55 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__56 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__56) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__56 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__56) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__56) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__56 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__57 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__57) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__57 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__57) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__57) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__57 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__58 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__58) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__58 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__58) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__58) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__58 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__59 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__59) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__59 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__59) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__59) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__59 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__6 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__6) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__6 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__6) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__6) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__6 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__60 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__60) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__60 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__60) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__60) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__60 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__61 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__61) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__61 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__61) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__61) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__61 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__62 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__62) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__62 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__62) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__62) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__62 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

