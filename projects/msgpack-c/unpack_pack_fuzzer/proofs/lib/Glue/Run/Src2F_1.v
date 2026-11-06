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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Src2F Require Import T_Src2F B_00 B_01 B_02 B_03.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import StdioWrite DrvShape DrvLib DrvEdges.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations W64 Val Mem FI St Step Plan PlanS SW DrvShape DrvLib DrvEdges.
Unset Lia Cache.

Definition LAY : layout := Layout X22 [X19].
Definition CDFLT : swcert := SWC T_DRV2 0%uint63 0 [] [].
Ltac sw_explore := repeat (apply Forall_cons || apply Forall_nil); (split; [|split]); try (vm_compute; reflexivity);
  intros HH; vm_compute in HH; try discriminate HH; vm_compute; reflexivity.

Record hyps (R : drun) : Prop := Hyps {
  h_ctab : ctab_ok SEGS R T_Src2F.CONTRACTS;
  h_file : file_pb R;
  h_mpf : forall m, r_MP R m -> fs_lookup (m_fs m) (r_p1 R) = Some (r_file R);
  h_famf : path_has_slash (r_p1 R) = false /\ path_is_dirref (r_p1 R) = false /\ (length (r_p1 R) < 4096)%nat /\ r_p1 R <> [];
  h_mnf : mnofork_ok SEGS R 294592%uint63 (c_apply (Contract 294592%uint63 (CtrA.malloc_apply SEGS 422892%uint63 554784%uint63 349792%uint63 554752%uint63 423056%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63)))));
  h_lib_r8 : lib_ok SEGS R (t_st T_LIBGEN_r8) (t_st R_LIBGEN_r8_RET);
  h_lib_r9 : lib_ok SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET)
}.

Lemma N_E_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.CTX C_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.PLAN (t_st T_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) C_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.OBLS (DR R (SX 2)) [] [(202%uint63, E_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0_1)] C_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.CTX HC) C_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.CTX C_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.PLAN (t_st T_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) C_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.OBLS (DR R (SX 2)) [(176%uint63, T_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0)] [] C_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.CTX HC) C_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0).
Lemma N_T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0) SWC_T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ab38_r8o2n1o7n1o1n6o3n2_s3_w0_e67bd0b67bd0 R H)].
Qed.

Lemma N_R_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0.CTX C_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0) C_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(106%uint63, T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1)] [] C_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1edd4_10000_r8o2n1o7n1o1n6o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.CTX C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.PLAN (t_st T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0) C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.OBLS (DR R (SX 2)) [] [(239%uint63, E_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0_1)] C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.CTX HC) C_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.CTX C_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.PLAN (t_st T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0) C_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.OBLS (DR R (SX 2)) [(206%uint63, T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0)] [] C_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.CTX HC) C_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_2_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0).
Lemma N_T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0) SWC_T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0 R H)].
Qed.

Lemma N_R_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(190%uint63, T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)] [] C_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1ee28_20000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0).
Lemma N_T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1) (t_st T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0) SWC_T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 2 [(CLit MSG_OOM)] (SX 2)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ab38_r9o2n1o7n1o1n9o3n2_s3_w0_e67bd0b67bd0 R H)].
Qed.

Lemma N_R_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (SWr 2 [(CLit MSG_OOM)] (SX 2))) [(224%uint63, T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1)] [] C_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_MF_1ee28_40000_r9o2n1o7n1o1n9o3n2_s3_w0_e0b0_0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1 (DR R (SX 0)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0) (DR R (SX 0)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.CTX C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.PLAN (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.OBLS (DR R (SX 0)) [] [(234%uint63, E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1)] C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.CTX HC) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_E_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1 (DR R (SX 2)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0) (DR R (SX 2)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.CTX C_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.PLAN (t_st T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0) C_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.OBLS (DR R (SX 2)) [] [(235%uint63, E_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1)] C_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.CTX HC) C_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_1 (DR R (SX 0)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0) (DR R (SX 0)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0.CTX C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0.PLAN (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0.OBLS (DR R (SX 0)) [] [(259%uint63, E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_1)] C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0.CTX HC) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_1 R H)|]; apply Forall_nil.
Qed.

Lemma N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1) (DR R (SX 0)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1.CTX C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1.PLAN (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1) C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1.OBLS (DR R (SX 0)) [(240%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0)] [] C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1.CTX HC) C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1).
Lemma N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1) SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1 1 [(CLit LINE0)] (SX 0)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1 R H)].
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(249%uint63, T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0RET R H).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(207%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 294592%uint63 (c_apply (Contract 294592%uint63 (CtrA.malloc_apply SEGS 422892%uint63 554784%uint63 349792%uint63 554752%uint63 423056%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Src2F.FORK_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0 (N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1).
Lemma N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1) SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1 1 [(CLit LINE0)] (SX 0)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k1 R H)].
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(250%uint63, T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z) _ R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0zRET R H).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(208%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w0_e0b0z R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 294592%uint63 (c_apply (Contract 294592%uint63 (CtrA.malloc_apply SEGS 422892%uint63 554784%uint63 349792%uint63 554752%uint63 423056%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HMNF eq_refl T_Src2F.FORK_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z (N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s1_w0_e0b0z_1 R H)).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0_1 (DR R (SX 0)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0) (DR R (SX 0)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0.CTX C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0.PLAN (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0) C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0.OBLS (DR R (SX 0)) [] [(287%uint63, E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0_1)] C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0.CTX HC) C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0_1 R H)|]; apply Forall_nil.
Qed.

Definition SWC_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1) (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0).
Lemma N_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1) (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0) SWC_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1 1 [(CLit LINE0)] (SX 0)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k0 R H)].
Qed.

Lemma N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0.CTX C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0.PLAN (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(273%uint63, T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1)] [] C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0.CTX HC) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(260%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bda_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0 T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0RET R H).
Qed.

Lemma N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2) (DR R (SWr 1 [(CLit LINE0)] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2.CTX C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2.PLAN (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2) C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2.OBLS (DR R (SWr 1 [(CLit LINE0)] (SX 0))) [(261%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0)] [] C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2.CTX HC) C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bd8_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2).
Lemma N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2) SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k2 R H)].
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(251%uint63, T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0RET R H).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) [(209%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 294592%uint63 (c_apply (Contract 294592%uint63 (CtrA.malloc_apply SEGS 422892%uint63 554784%uint63 349792%uint63 554752%uint63 423056%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit LINE0)] (SX 0)))) HMNF eq_refl T_Src2F.FORK_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0 (N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s2_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0_1 (R : drun) (H : hyps R) : ENODE SEGS R E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0_1 (DR R (SX 0)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0) (DR R (SX 0)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0.CTX C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0.PLAN (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0) C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0.OBLS (DR R (SX 0)) [] [(293%uint63, E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0_1)] C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0.CTX HC) C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0_1 R H)|]; apply Forall_nil.
Qed.

Definition SWC_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1) (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0).
Lemma N_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1) (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0) SWC_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1 1 [(CLit (lines 2))] (SX 0)); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k0 R H)].
Qed.

Lemma N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0.CTX C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0.PLAN (t_st T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(284%uint63, T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1)] [] C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0.WF ITAB_ok (contracts_ok_of SEGS R C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0.CTX HC) C_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(267%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w67bdc_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0 T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0RET R H).
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(268%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s1_w67bda_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0 T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0RET R H).
Qed.

Lemma N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3) (DR R (SWr 1 [(CLit (lines 2))] (SX 0))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3.CTX C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3.PLAN (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3) C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3.OBLS (DR R (SWr 1 [(CLit (lines 2))] (SX 0))) [(262%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0)] [] C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3.CTX HC) C_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s2_w67bd8_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Definition SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1 : swcert := sw_cert SEGS ITAB LAY (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3).
Lemma N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  apply (node_sw_b SEGS R ITAB LAY ITAB_ok (t_st T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1) (t_st T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3) SWC_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0))); [vm_cast_no_check (@eq_refl bool true) | exact (N_T_SWRET_4ae4c_r10o5n0o7n1o1n12o3n2_s0_w67bd8_e0b0_k3 R H)].
Qed.

Lemma N_R_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET (R : drun) (H : hyps R) : NODE SEGS R R_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET.CTX C_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET.PLAN R_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET C_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(252%uint63, T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1)] [] C_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET.WF ITAB_ok (contracts_ok_of SEGS R C_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET.CTX HC) C_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_SW_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET_1 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_lib SEGS R (t_st T_LIBGEN_r9) (t_st R_LIBGEN_r9_RET) (t_st T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0) (mk_subst SG_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0) _ R_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HLIB_r9 ltac:(vm_compute; reflexivity) T_Src2F.LIBENT_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 T_Src2F.INST_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0).
  - vm_compute. reflexivity.
  - exact (N_R_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0RET R H).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) [(210%uint63, T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.CHK).
  - apply (obls_file_sound R HF C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1.OBLS); vm_compute; reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [exact (N_T_LIB_r10o5n0o7n1o1n12o3n2_s3_w0_e0b0 R H)|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_mnofork SEGS R 294592%uint63 (c_apply (Contract 294592%uint63 (CtrA.malloc_apply SEGS 422892%uint63 554784%uint63 349792%uint63 554752%uint63 423056%uint63 (VIns 4%uint63 4%uint63 (VIns 2%uint63 2%uint63 (VIns 1%uint63 1%uint63 (VIns 0%uint63 1%uint63 (VL (wp 0%uint63)) (VBlob false 6%uint63 (VL (wp 0%uint63)) 1%uint63)) (VL (wp 0%uint63))) (VBlob false 6%uint63 (VL (wp 2%uint63)) 2%uint63)) (VBlob false 6%uint63 (VL (wp 4%uint63)) 4%uint63))))) (t_st T_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_0) (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1) (DR R (SWr 1 [(CLit LINE0)] (SWr 1 [(CLit (lines 2))] (SX 0)))) HMNF eq_refl T_Src2F.FORK_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0 (N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s3_w0_e0b0_1 R H)).
Qed.

Lemma N_R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0 (R : drun) (H : hyps R) : NODE SEGS R (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) (DR R (XC (r_file R))).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.PLAN (t_st R_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.OBLS (DR R (XC (r_file R))) [(203%uint63, T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0); (204%uint63, T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0)] [] C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.WF ITAB_ok (contracts_ok_of SEGS R C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CTX HC) C_MF_1f0b4_n_c40000_r9o5n0o7n1o1n9o3n2_s4_w0_e0b0_0.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_0_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_cons; [(eapply (edge_xc SEGS R HF _ _); [vm_compute; reflexivity | exact (N_T_EXIT_2_r8o5n0o7n1o1n6o3n2_s0_w0_e0b0 R H)])|]; apply Forall_nil.
  - reflexivity.
  - apply Forall_nil.
Qed.

Lemma N_E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30_1 (R : drun) (H : hyps R) : ENODE SEGS R E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30_1 (DR R (SX 0)).
Proof. eapply (node_exit SEGS R); [vm_compute; reflexivity | reflexivity]. Qed.

Lemma N_T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30 (R : drun) (H : hyps R) : NODE SEGS R (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30) (DR R (SX 0)).
Proof.
  pose proof (h_ctab R H) as HC. pose proof (h_file R H) as HF. pose proof (h_mpf R H) as MPF. pose proof (h_famf R H) as FAMF. pose proof (h_mnf R H) as HMNF. pose proof (h_lib_r8 R H) as HLIB_r8. pose proof (h_lib_r9 R H) as HLIB_r9.
  apply (node_cert SEGS R C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30.CTX C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30.PLAN (t_st T_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30) C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30.OBLS (DR R (SX 0)) [] [(294%uint63, E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30_1)] C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30.WF ITAB_ok (contracts_ok_of SEGS R C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30.CTX HC) C_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30.CHK).
  - apply Forall_nil.
  - reflexivity.
  - reflexivity.
  - apply Forall_nil.
  - reflexivity.
  - apply Forall_cons; [exact (N_E_SWRET_4a884_r8o5n0o7n1o1n6o3n2_s0_w67bd8_e0b0_k30_k30_1 R H)|]; apply Forall_nil.
Qed.

