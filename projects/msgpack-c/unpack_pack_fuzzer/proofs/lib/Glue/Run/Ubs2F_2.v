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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require Import T_Ubs2F B_00 B_01 B_02 B_03.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Ubs2F_1.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1) (t_st T_SWRET_4c098_r8o5n0o7n1o1n6o3n2_s0_w693e8_e0b0_k30_k30).
Lemma N_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1) (t_st T_SWRET_4c098_r8o5n0o7n1o1n6o3n2_s0_w693e8_e0b0_k30_k30) SWC_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1 1 [(CLit (lines 3))] (SX 0)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c098_r8o5n0o7n1o1n6o3n2_s0_w693e8_e0b0_k30_k30 R H)].
Qed.

Lemma N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0.CTX C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0.PLAN (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(290%uint63, T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1)] [] C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0.CTX HC) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(277%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w693ee_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Ubs2F.LIBENT_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0 T_Ubs2F.INST_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0RET R H).
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(278%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w693ec_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Ubs2F.LIBENT_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0 T_Ubs2F.INST_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0RET R H).
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(269%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w693ea_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Ubs2F.LIBENT_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0 T_Ubs2F.INST_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0RET R H).
Qed.

Lemma N_T_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4) (DR R (SWr 1 [(CLit (lines 3))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4.CTX C_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4.PLAN (t_st T_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4) C_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4.OBLS (DR R (SWr 1 [(CLit (lines 3))] (SX 0))) [(263%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0)] [] C_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4.CTX HC) C_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w693e8_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1) (t_st T_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4).
Lemma N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1) (t_st T_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4) SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c660_r10o5n0o7n1o1n12o3n2_s0_w693e8_e0b0_k4 R H)].
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(253%uint63, T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Ubs2F.LIBENT_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 T_Ubs2F.INST_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0RET R H).
Qed.

Lemma N_R_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(211%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)] [] C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (t_st R_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (t_st R_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (N_R_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 R H)).
Qed.

Lemma N_T_POSTREAD_40000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_40000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_40000_BGBlob.CTX C_POSTREAD_40000_BGBlob.PLAN (t_st T_POSTREAD_40000_BGBlob) C_POSTREAD_40000_BGBlob.OBLS (DR R (POST (r_file R))) [(244%uint63, T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (245%uint63, T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (246%uint63, T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (247%uint63, T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (248%uint63, T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)] [] C_POSTREAD_40000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_40000_BGBlob.CTX HC) C_POSTREAD_40000_BGBlob.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0).
Lemma N_T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0) SWC_T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0 R H)].
Qed.

Lemma N_R_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(274%uint63, T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)] [] C_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1f418_80000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(207%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(208%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(209%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(210%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(211%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)] [] C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (t_st R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (N_R_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 R H)).
Qed.

Lemma N_T_POSTREAD_80000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_80000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_80000_BGBlob.CTX C_POSTREAD_80000_BGBlob.PLAN (t_st T_POSTREAD_80000_BGBlob) C_POSTREAD_80000_BGBlob.OBLS (DR R (POST (r_file R))) [(279%uint63, T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (280%uint63, T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (281%uint63, T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (282%uint63, T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (283%uint63, T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)] [] C_POSTREAD_80000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_80000_BGBlob.CTX HC) C_POSTREAD_80000_BGBlob.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c80000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0).
Lemma N_T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0) SWC_T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0 R H)].
Qed.

Lemma N_R_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(297%uint63, T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)] [] C_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1f418_100000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(207%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(208%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(209%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(210%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(211%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)] [] C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (t_st R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (N_R_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 R H)).
Qed.

Lemma N_T_POSTREAD_100000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_100000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_100000_BGBlob.CTX C_POSTREAD_100000_BGBlob.PLAN (t_st T_POSTREAD_100000_BGBlob) C_POSTREAD_100000_BGBlob.OBLS (DR R (POST (r_file R))) [(298%uint63, T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (299%uint63, T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (300%uint63, T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (301%uint63, T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (302%uint63, T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)] [] C_POSTREAD_100000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_100000_BGBlob.CTX HC) C_POSTREAD_100000_BGBlob.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c100000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0).
Lemma N_T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0) SWC_T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0 R H)].
Qed.

Lemma N_R_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(306%uint63, T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)] [] C_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1f418_200000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(207%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(208%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(209%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(210%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(211%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)] [] C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (t_st R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (N_R_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 R H)).
Qed.

Lemma N_T_POSTREAD_200000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_200000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_200000_BGBlob.CTX C_POSTREAD_200000_BGBlob.PLAN (t_st T_POSTREAD_200000_BGBlob) C_POSTREAD_200000_BGBlob.OBLS (DR R (POST (r_file R))) [(307%uint63, T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (308%uint63, T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (309%uint63, T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (310%uint63, T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (311%uint63, T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)] [] C_POSTREAD_200000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_200000_BGBlob.CTX HC) C_POSTREAD_200000_BGBlob.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c200000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0).
Lemma N_T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0) SWC_T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c34c_r9o2n1o7n1o1n9o3n2_s3_w0_e693e0b693e0 R H)].
Qed.

Lemma N_R_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(315%uint63, T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)] [] C_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1f418_400000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(207%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(208%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(209%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(210%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.PLAN (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) [(211%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0)] [] C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CTX HC) C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s4_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (t_st R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 3))] (SX 0)))) HMNF eq_refl T_Ubs2F.FORK_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 (N_R_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_1 R H)).
Qed.

Lemma N_T_POSTREAD_400000_BGBlob (R : drun) (H : hyps R) : NODE SEGS R (t_st T_POSTREAD_400000_BGBlob) (DR R (POST (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_POSTREAD_400000_BGBlob.CTX C_POSTREAD_400000_BGBlob.PLAN (t_st T_POSTREAD_400000_BGBlob) C_POSTREAD_400000_BGBlob.OBLS (DR R (POST (r_file R))) [(316%uint63, T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0); (317%uint63, T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z); (318%uint63, T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0); (319%uint63, T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0); (320%uint63, T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0)] [] C_POSTREAD_400000_BGBlob.WF ITAB_ok (contracts_ok_of SEGS R C_POSTREAD_400000_BGBlob.CTX HC) C_POSTREAD_400000_BGBlob.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_post SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_MF_1f6a4_n_c400000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

