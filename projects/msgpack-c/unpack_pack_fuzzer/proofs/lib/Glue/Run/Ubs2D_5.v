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
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue.Run Require Import Ubs2D_1 Ubs2D_2 Ubs2D_3 Ubs2D_4.
Unset Nia Cache. Unset Nra Cache.

Definition SWC_T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1) (DR R (SWr 2 [] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 2 [] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Lemma N_T_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230) (DR R (SWr 2 [] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.CTX C_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.PLAN (t_st T_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230) C_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.OBLS (DR R (SWr 2 [] (SX 2))) [(243%uint63, T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1)] [] C_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.CTX HC) C_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62) (t_st T_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62) (t_st T_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c978_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230 R H)].
Qed.

Lemma N_E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.CTX C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.PLAN (t_st T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka) C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.OBLS (DR R (SX 2)) [] [(258%uint63, E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka_1)] C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.CTX HC) C_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka.CTX C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka.PLAN (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka) C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka.OBLS (DR R (SX 2)) [(254%uint63, T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka)] [] C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka.CTX HC) C_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r9o4n0o7n1o1n9o3n2_s3_w0_e0b0_ka R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka).
Lemma N_T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka) SWC_T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 2 [(CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_ka R H)].
Qed.

Lemma N_T_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230) (DR R (SWr 2 [(CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.CTX C_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.PLAN (t_st T_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230) C_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.OBLS (DR R (SWr 2 [(CLit NL)] (SX 2))) [(245%uint63, T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1)] [] C_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.CTX HC) C_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63) (t_st T_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63) (t_st T_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63 2 [(CLit MSG_RDERR_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4d398_r9o4n0o7n1o1n9o3n2_s57ed8_w0_ev1_0x230bv1_0x230 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9) (t_st T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r9o4n0o7n1o1n9o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Lemma N_R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.CTX C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.PLAN (t_st R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1) C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.OBLS (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))) [(104%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1); (105%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10); (106%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11); (107%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12); (108%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13); (109%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14); (110%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15); (111%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16); (112%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17); (113%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18); (114%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19); (115%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2); (116%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20); (117%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21); (118%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22); (119%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23); (120%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24); (121%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25); (122%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26); (123%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27); (124%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28); (125%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29); (126%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3); (127%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30); (128%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31); (129%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32); (130%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33); (131%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34); (132%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35); (133%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36); (134%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37); (135%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38); (136%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39); (137%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4); (138%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40); (139%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41); (140%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42); (141%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43); (142%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44); (143%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45); (144%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46); (145%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47); (146%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48); (147%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49); (148%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5); (149%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50); (150%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51); (151%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52); (152%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53); (153%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54); (154%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55); (155%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56); (156%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57); (157%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58); (158%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59); (159%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6); (160%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60); (161%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61); (162%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62); (163%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63); (164%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7); (165%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8); (166%uint63, T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9)] [] C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.CTX HC) C_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit [99; 108; 105; 58; 32; 114; 101; 97; 100; 32; 101; 114; 114; 111; 114; 32; 111; 110; 32; 10])] (SX 2))); [vm_compute; reflexivity | exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_1 R H)])|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_10 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_11 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_12 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_13 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_14 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_15 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_16 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_17 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_18 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_19 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_2 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_20 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_21 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_22 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_23 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_24 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_25 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_26 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_27 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_28 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_29 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_3 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_30 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_31 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_32 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_33 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_34 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_35 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_36 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_37 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_38 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_39 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_4 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_40 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_41 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_42 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_43 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_44 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_45 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_46 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_47 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_48 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_49 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_5 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_50 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_51 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_52 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_53 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_54 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_55 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_56 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_57 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_58 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_59 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_6 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_60 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_61 R H)|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SWr 2 [] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_62 R H)])|]; apply Forall_cons; [(apply (node_eqv_f SEGS R _ (SWr 2 [(CLit MSG_RDERR_PRE); CP1] (SWr 2 [(CLit NL)] (SX 2)))); [vm_compute; reflexivity | exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_63 R H)])|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_7 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_8 R H)|]; apply Forall_cons; [exact (N_T_SW_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1_9 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_mnofork SEGS R 300740%uint63 (c_apply (Contract 300740%uint63 (CtrA.malloc_apply SEGS 429036%uint63 560928%uint63 355944%uint63 560896%uint63 429200%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0) (t_st R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_0) (t_st R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))) HMNF eq_refl T_Ubs2D.FORK_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0 (N_R_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0_1 R H)).
Qed.

Lemma N_R_OPEN__0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_OPEN__0) (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_OPEN__0.CTX C_OPEN__0.PLAN (t_st R_OPEN__0) C_OPEN__0.OBLS (DR R (SWr 2 [(CLit MSG_RDERR_PRE); CP1; (CLit NL)] (SX 2))) [(101%uint63, T_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0)] [] C_OPEN__0.WF ITAB_ok (contracts_ok_of SEGS R C_OPEN__0.CTX HC) C_OPEN__0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_MF_1f3c4_10000_r8o4n0o7n1o1n6o3n2_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.CTX C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.PLAN (t_st T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63) C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.OBLS (DR R (SX 2)) [] [(255%uint63, E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63_1)] C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.CTX HC) C_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_famd R H) as FAMD. pose proof (h_mnf R H) as HMNF.
  apply (node_cert SEGS R C_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.CTX C_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.PLAN (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) C_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.OBLS (DR R (SX 2)) [(251%uint63, T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63)] [] C_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.CTX HC) C_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o7n1o1n6o5n0o3n2_s0_w0_e0b0_k63 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_OPENERR__1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__1) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__1) (DR R (SWr 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__1) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__1 2 [(CLit [99; 108; 105; 58; 32; 99; 97; 110; 110; 111; 116; 32; 111; 112; 101; 110; 32; 10])] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__10 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__10) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__10 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__10) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__10) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__10 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__11 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__11) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__11 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__11) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__11) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__11 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__12 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__12) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__12 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__12) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__12) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__12 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__13 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__13) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__13 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__13) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__13) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__13 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

Definition SWC_T_SW_OPENERR__14 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_OPENERR__14) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63).
Lemma N_T_SW_OPENERR__14 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_OPENERR__14) (DR R (SWr 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_OPENERR__14) (t_st T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63) SWC_T_SW_OPENERR__14 2 [(CLit MSG_OPEN_PRE); CP1; (CLit NL)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4c7a8_r8o7n1o1n6o5n0o3n2_s693e0_w0_ev1_0x230bv1_0x230_k63 R H)].
Qed.

