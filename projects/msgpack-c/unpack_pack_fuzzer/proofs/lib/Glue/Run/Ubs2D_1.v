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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2D Require Import T_Ubs2D B_00.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

Record hyps (R : drun) : Prop := Hyps {
  h_ctab : ctab_ok SEGS R T_Ubs2D.CONTRACTS;
  h_famd : path_is_dirref (r_p1 R) = true;
  h_mnf : mnofork_ok SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63)))))
}.

Lemma N_E_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.CTX C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.PLAN (t_st T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0) C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.OBLS (DR R (SX 2)) [] [(250%uint63, E_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0_1)] C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.CTX HC) C_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.CTX C_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.PLAN (t_st T_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0) C_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.OBLS (DR R (SX 2)) [(239%uint63, T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0)] [] C_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.CTX HC) C_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c34c_r8o4n0o7n1o1n6o3n2_s3_w0_e693e0b693e0 R H)].
Qed.

Lemma N_R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.CTX C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0) C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(103%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1)] [] C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.CTX C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.PLAN (t_st T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63) C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.OBLS (DR R (SX 2)) [] [(257%uint63, E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63_1)] C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.CTX HC) C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.CTX C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.PLAN (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.OBLS (DR R (SX 2)) [(253%uint63, T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63)] [] C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.CTX HC) C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_k63 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1) (DR R (SWr 2 [(CLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 10])] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1 2 [(CLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 10])] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

