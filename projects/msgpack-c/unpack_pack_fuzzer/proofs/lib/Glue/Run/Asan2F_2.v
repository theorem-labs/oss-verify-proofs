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

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Asan2F_1.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1) (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k2).
Lemma N_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1) (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k2) SWC_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k2 R H)].
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(205%uint63, T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0RET R H).
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(242%uint63, T_EXIT_0_r8o5n0o1n9o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d4_e0b0)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_0_r8o5n0o1n9o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d4_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0RET R H).
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(238%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d2_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0RET R H).
Qed.

Lemma N_T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3.CTX C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3.PLAN (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3) C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(228%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0)] [] C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3.CTX HC) C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1) (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3).
Lemma N_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1) (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3) SWC_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k3 R H)].
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(206%uint63, T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0RET R H).
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(248%uint63, T_EXIT_0_r8o5n0o1n9o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d6_e0b0)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_0_r8o5n0o1n9o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d6_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0RET R H).
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(244%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w60d3d4_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0RET R H).
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(239%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w60d3d2_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0RET R H).
Qed.

Lemma N_T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4.CTX C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4.PLAN (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4) C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(229%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0)] [] C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4.CTX HC) C_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w60d3d0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1) (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4).
Lemma N_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1) (t_st T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4) SWC_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3bf8_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w60d3d0_e0b0_q69817_k4 R H)].
Qed.

Lemma N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET.CTX C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET.PLAN R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(207%uint63, T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1)] [] C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET.CTX HC) C_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r12) (t_st R_LIBGEN_r12_RET) (t_st T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0) (mk_subst SG_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0) _ R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HLIB_r12 ltac:(vm_compute; reflexivity) T_Asan2F.LIBENT_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 T_Asan2F.INST_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0RET R H).
Qed.

Lemma N_E_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8.CTX C_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8.PLAN (t_st T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8) C_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8.OBLS (DR R (SX 2)) [] [(222%uint63, E_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8_1)] C_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8.CTX HC) C_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367.CTX C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367.PLAN (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367) C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367.OBLS (DR R (SX 2)) [(195%uint63, T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8)] [] C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367.CTX HC) C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_POSTREAD_10000_BGBlob_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_POSTREAD_10000_BGBlob_1) (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367).
Lemma N_T_SW_POSTREAD_10000_BGBlob_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_POSTREAD_10000_BGBlob_1) (DR R (SWr 2 [(CLit MSG_SHORT)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_POSTREAD_10000_BGBlob_1) (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367) SWC_T_SW_POSTREAD_10000_BGBlob_1 2 [(CLit MSG_SHORT)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367 R H)].
Qed.

Lemma N_T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1.CTX C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1.PLAN (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1) C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1.OBLS (DR R (SX 2)) [(195%uint63, T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8)] [] C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1.CTX HC) C_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o5n0o1n12o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e60d3c8b60d3c8 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_POSTREAD_10000_BGBlob_2 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_POSTREAD_10000_BGBlob_2) (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1).
Lemma N_T_SW_POSTREAD_10000_BGBlob_2 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_POSTREAD_10000_BGBlob_2) (DR R (SWr 2 [(CLit MSG_CFG)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_POSTREAD_10000_BGBlob_2) (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1) SWC_T_SW_POSTREAD_10000_BGBlob_2 2 [(CLit MSG_CFG)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_qeaaf1 R H)].
Qed.

Lemma N_T_POSTREAD_10000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_10000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_10000_BGBlob.CTX C_POSTREAD_10000_BGBlob.PLAN (t_st T_POSTREAD_10000_BGBlob) C_POSTREAD_10000_BGBlob.OBLS (DR R (POST (r_file R))) [(107%uint63, T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (108%uint63, T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (109%uint63, T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (110%uint63, T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (111%uint63, T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0); (112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0); (182%uint63, T_SW_POSTREAD_10000_BGBlob_1); (183%uint63, T_SW_POSTREAD_10000_BGBlob_2)] [] C_POSTREAD_10000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_10000_BGBlob.CTX HC) C_POSTREAD_10000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_10000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r10o5n0o1n15o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_SW_POSTREAD_10000_BGBlob_1 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_SW_POSTREAD_10000_BGBlob_2 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_POSTREAD_10000_BGUnk_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_POSTREAD_10000_BGUnk_1) (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367).
Lemma N_T_SW_POSTREAD_10000_BGUnk_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_POSTREAD_10000_BGUnk_1) (DR R (SWr 2 [(CLit MSG_SHORT)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_POSTREAD_10000_BGUnk_1) (t_st T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367) SWC_T_SW_POSTREAD_10000_BGUnk_1 2 [(CLit MSG_SHORT)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3b0c_r10o5n0o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e60d3c8b60d3c8_q0d367 R H)].
Qed.

Lemma N_T_POSTREAD_10000_BGUnk (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_10000_BGUnk) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_10000_BGUnk.CTX C_POSTREAD_10000_BGUnk.PLAN (t_st T_POSTREAD_10000_BGUnk) C_POSTREAD_10000_BGUnk.OBLS (DR R (POST (r_file R))) [(184%uint63, T_SW_POSTREAD_10000_BGUnk_1)] [] C_POSTREAD_10000_BGUnk.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_10000_BGUnk.CTX HC) C_POSTREAD_10000_BGUnk.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_SW_POSTREAD_10000_BGUnk_1 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_20000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_20000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_20000_BGBlob.CTX C_POSTREAD_20000_BGBlob.PLAN (t_st T_POSTREAD_20000_BGBlob) C_POSTREAD_20000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_20000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_20000_BGBlob.CTX HC) C_POSTREAD_20000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_20000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_40000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_40000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_40000_BGBlob.CTX C_POSTREAD_40000_BGBlob.PLAN (t_st T_POSTREAD_40000_BGBlob) C_POSTREAD_40000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_40000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_40000_BGBlob.CTX HC) C_POSTREAD_40000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_40000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_80000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_80000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_80000_BGBlob.CTX C_POSTREAD_80000_BGBlob.PLAN (t_st T_POSTREAD_80000_BGBlob) C_POSTREAD_80000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_80000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_80000_BGBlob.CTX HC) C_POSTREAD_80000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_80000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_100000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_100000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_100000_BGBlob.CTX C_POSTREAD_100000_BGBlob.PLAN (t_st T_POSTREAD_100000_BGBlob) C_POSTREAD_100000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_100000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_100000_BGBlob.CTX HC) C_POSTREAD_100000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_100000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_200000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_200000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_200000_BGBlob.CTX C_POSTREAD_200000_BGBlob.PLAN (t_st T_POSTREAD_200000_BGBlob) C_POSTREAD_200000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_200000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_200000_BGBlob.CTX HC) C_POSTREAD_200000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_200000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_400000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_400000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_400000_BGBlob.CTX C_POSTREAD_400000_BGBlob.PLAN (t_st T_POSTREAD_400000_BGBlob) C_POSTREAD_400000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_400000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_400000_BGBlob.CTX HC) C_POSTREAD_400000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_400000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_800000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_800000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_800000_BGBlob.CTX C_POSTREAD_800000_BGBlob.PLAN (t_st T_POSTREAD_800000_BGBlob) C_POSTREAD_800000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_800000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_800000_BGBlob.CTX HC) C_POSTREAD_800000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_800000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_1000000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_1000000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_1000000_BGBlob.CTX C_POSTREAD_1000000_BGBlob.PLAN (t_st T_POSTREAD_1000000_BGBlob) C_POSTREAD_1000000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_1000000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_1000000_BGBlob.CTX HC) C_POSTREAD_1000000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_1000000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_2000000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_2000000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_2000000_BGBlob.CTX C_POSTREAD_2000000_BGBlob.PLAN (t_st T_POSTREAD_2000000_BGBlob) C_POSTREAD_2000000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_2000000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_2000000_BGBlob.CTX HC) C_POSTREAD_2000000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_2000000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_POSTREAD_4000000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_4000000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_4000000_BGBlob.CTX C_POSTREAD_4000000_BGBlob.PLAN (t_st T_POSTREAD_4000000_BGBlob) C_POSTREAD_4000000_BGBlob.OBLS (DR R (POST (r_file R))) [(112%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0); (113%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z); (114%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0); (115%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (116%uint63, T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0)] [] C_POSTREAD_4000000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_4000000_BGBlob.CTX HC) C_POSTREAD_4000000_BGBlob.CHK).
  - apply (obls_file_sound R HF C_POSTREAD_4000000_BGBlob.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_LIB_r13o5n0o1n21o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN (t_st T_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) C_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS (DR R (SX 2)) [] [(274%uint63, E_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1)] C_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) C_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2.CTX C_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2.PLAN (t_st T_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2) C_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2.OBLS (DR R (SX 2)) [(273%uint63, T_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2.CTX HC) C_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1) (t_st T_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2).
Lemma N_T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1) (DR R (SWr 2 [(CLit MSG_BIG)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1) (t_st T_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2) SWC_T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 2 [(CLit MSG_BIG)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q3eab2 R H)].
Qed.

Lemma N_T_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 0 67108864)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 270%uint63 T_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 0 67108864)) [(269%uint63, T_POSTREAD_4000000_BGBlob); (270%uint63, T_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (271%uint63, T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1)] [] C_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 0%nat 67108864 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_4000000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 0%nat 67108864 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_SW_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0_1 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 1 33554432)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 268%uint63 T_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 1 33554432)) [(267%uint63, T_POSTREAD_2000000_BGBlob); (268%uint63, T_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (269%uint63, T_POSTREAD_4000000_BGBlob); (270%uint63, T_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 1%nat 33554432 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_2000000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 1%nat 33554432 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 0%nat 67108864 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_4000000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 1%nat 33554432 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_4000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 2 16777216)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 266%uint63 T_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 2 16777216)) [(265%uint63, T_POSTREAD_1000000_BGBlob); (266%uint63, T_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (267%uint63, T_POSTREAD_2000000_BGBlob); (268%uint63, T_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 2%nat 16777216 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_1000000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 2%nat 16777216 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 1%nat 33554432 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_2000000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 2%nat 16777216 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_2000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 3 8388608)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 264%uint63 T_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 3 8388608)) [(263%uint63, T_POSTREAD_800000_BGBlob); (264%uint63, T_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (265%uint63, T_POSTREAD_1000000_BGBlob); (266%uint63, T_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 3%nat 8388608 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_800000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 3%nat 8388608 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 2%nat 16777216 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_1000000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 3%nat 8388608 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_1000000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 4 4194304)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 262%uint63 T_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 4 4194304)) [(261%uint63, T_POSTREAD_400000_BGBlob); (262%uint63, T_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (263%uint63, T_POSTREAD_800000_BGBlob); (264%uint63, T_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 4%nat 4194304 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_400000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 4%nat 4194304 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 3%nat 8388608 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_800000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 4%nat 4194304 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_800000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 5 2097152)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 250%uint63 T_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 5 2097152)) [(249%uint63, T_POSTREAD_200000_BGBlob); (250%uint63, T_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (261%uint63, T_POSTREAD_400000_BGBlob); (262%uint63, T_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 5%nat 2097152 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_200000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 5%nat 2097152 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 4%nat 4194304 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_400000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 5%nat 2097152 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_400000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 6 1048576)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 241%uint63 T_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 6 1048576)) [(240%uint63, T_POSTREAD_100000_BGBlob); (241%uint63, T_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (249%uint63, T_POSTREAD_200000_BGBlob); (250%uint63, T_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 6%nat 1048576 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_100000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 6%nat 1048576 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 5%nat 2097152 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_200000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 6%nat 1048576 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_200000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 7 524288)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 197%uint63 T_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 7 524288)) [(196%uint63, T_POSTREAD_80000_BGBlob); (197%uint63, T_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (240%uint63, T_POSTREAD_100000_BGBlob); (241%uint63, T_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 7%nat 524288 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_80000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 7%nat 524288 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 6%nat 1048576 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_100000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 7%nat 524288 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_100000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0) (DR R (RDn (r_file R) 8 262144)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_loop SEGS R C_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX C_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.PLAN C_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.OBLS 106%uint63 T_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 (DR R (RDn (r_file R) 8 262144)) [(105%uint63, T_POSTREAD_40000_BGBlob); (106%uint63, T_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0); (196%uint63, T_POSTREAD_80000_BGBlob); (197%uint63, T_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CTX HC) eq_refl eq_refl C_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 8%nat 262144 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_40000_BGBlob R H)]))|]; apply Forall_cons; [(left; reflexivity)|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 8%nat 262144 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 7%nat 524288 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_80000_BGBlob R H)])]))|]; apply Forall_cons; [(right; (eapply (edge_rd SEGS R HF _ 8%nat 262144 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_80000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)]))|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_OPEN__0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__0) (DR R (RDn (r_file R) 10 65536)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_OPEN__0.CTX C_OPEN__0.PLAN (t_st R_OPEN__0) C_OPEN__0.OBLS (DR R (RDn (r_file R) 10 65536)) [(102%uint63, T_POSTREAD_10000_BGBlob); (103%uint63, T_POSTREAD_10000_BGUnk); (104%uint63, T_POSTREAD_20000_BGBlob); (105%uint63, T_POSTREAD_40000_BGBlob); (106%uint63, T_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0)] [] C_OPEN__0.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__0.CTX HC) C_OPEN__0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_rd SEGS R HF _ 10%nat 65536 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_10000_BGBlob R H)])|]; apply Forall_cons; [(eapply (edge_rd SEGS R HF _ 10%nat 65536 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_10000_BGUnk R H)])|]; apply Forall_cons; [(eapply (edge_rd SEGS R HF _ 10%nat 65536 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 9%nat 131072 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_20000_BGBlob R H)])])|]; apply Forall_cons; [(eapply (edge_rd SEGS R HF _ 10%nat 65536 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 9%nat 131072 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 8%nat 262144 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_POSTREAD_40000_BGBlob R H)])])])|]; apply Forall_cons; [(eapply (edge_rd SEGS R HF _ 10%nat 65536 _ ltac:(lia)); [vm_compute; reflexivity | (eapply (edge_rd SEGS R HF _ 9%nat 131072 _ ltac:(lia)); [vm_compute; reflexivity | exact (N_T_RLOOP_40000_BGBlob_r10o2n1o1n18o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s3_w0_e0b0 R H)])])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.CTX C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.PLAN (t_st T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.OBLS (DR R (SX 2)) [] [(233%uint63, E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1)] C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.CTX HC) C_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_lib_r12 R H) as HLIB_r12. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63.CTX C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63.PLAN (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63.OBLS (DR R (SX 2)) [(230%uint63, T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63)] [] C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63.CTX HC) C_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s0_w0_e0b0_k63 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__1) (DR R (SWr 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__1) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__1 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__10 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__10) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__10 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__10) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__10) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__10 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__11 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__11) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63).
Lemma N_T_SW_OPENERR__11 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__11) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__11) (t_st T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63) SWC_T_SW_OPENERR__11 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_c3de0_r8o1n12o5n0o7n1o15n2o10n0o11n0o12n0o13n0o14n1o16n0o17n0_s60d3c8_w0_ev1_0x250bv1_0x250_q46cc9_k63 R H)].
Qed.

