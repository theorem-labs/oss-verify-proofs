(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Monad Specs Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs StepSoundBase StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Img Require Import ImgUbs ItabUbs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA DefsM Defs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2F Require T_Ubs2F.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2L Require T_Ubs2L.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require T_Ubs2U.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require T_Ubs2UE.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U Require B_00 B_02.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE Require B_00 B_01 B_02 B_03 B_04 B_06 B_07 B_09 B_10 B_13 B_14 B_15 B_16.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Glue Require Import Nodes CertSound Ops CtrSys DrvShape DrvRoot DrvLib LibLib LibFamily.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP StepB StepS PlanS FXN CertS Ops CtrS DrvLib LibLib LibFamily.
Open Scope Z_scope.
Unset Lia Cache.
Module C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.
Module C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.
Module C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_00.C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.
Module C_EXECRET_rc0_m1_n14_w0111234 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_00.C_EXECRET_rc0_m1_n14_w0111234.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.
Module C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.
Module C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.
Module C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2U.B_02.C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.
Module C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.
Module C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.
Module C_UW_2037c_48285_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_03.C_UW_2037c_48285_w7_r14_pP_L0.
Module C_UW_2037c_48285_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_04.C_UW_2037c_48285_w8_r15_pv_L0.
Module C_UW_236d8_0c366_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_0c366_w6_r13_pP_L0.
Module C_UW_236d8_0c366_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_0c366_w7_r14_pv_L0.
Module C_UW_236d8_52706_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_52706_w6_r13_pP_L0.
Module C_UW_236d8_52706_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_06.C_UW_236d8_52706_w7_r14_pv_L0.
Module C_UW_236d8_c92f2_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_c92f2_w6_r13_pP_L0.
Module C_UW_236d8_c92f2_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_236d8_c92f2_w7_r14_pv_L0.
Module C_UW_52944_4a174_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_4a174_w6_r13_pP_L0.
Module C_UW_52944_4a174_w7_r14_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_07.C_UW_52944_4a174_w7_r14_pv_L0.
Module C_UW_52944_7e112_w6_r13_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_7e112_w6_r13_pP_L0.
Module C_UW_52944_7e112_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_13.C_UW_52944_7e112_w7_r14_pP_L0.
Module C_UW_52944_cb62d_w7_r14_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_14.C_UW_52944_cb62d_w7_r14_pP_L0.
Module C_UW_52944_cb62d_w8_r15_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_15.C_UW_52944_cb62d_w8_r15_pv_L0.
Module C_XA_2037c_48285_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_2037c_48285_blk_w7_r14_L0.
Module C_XA_2037c_48285_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_01.C_XA_2037c_48285_p682f0_w6_r13_pP.
Module C_XA_236d8_0c366_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_0c366_blk_w7_r14_L0.
Module C_XA_236d8_0c366_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_0c366_p682f0_w6_r13_pP.
Module C_XA_236d8_52706_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_52706_blk_w7_r14_L0.
Module C_XA_236d8_52706_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_52706_p682f0_w6_r13_pP.
Module C_XA_236d8_c92f2_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_c92f2_blk_w7_r14_L0.
Module C_XA_236d8_c92f2_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_236d8_c92f2_p682f0_w6_r13_pP.
Module C_XA_52944_4a174_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_4a174_blk_w7_r14_L0.
Module C_XA_52944_4a174_p682f0_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_02.C_XA_52944_4a174_p682f0_w6_r13_pP.
Module C_XA_52944_7e112_blk_w7_r14_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_7e112_blk_w7_r14_L0.
Module C_XA_52944_7e112_p68250_w6_r13_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_XA_52944_7e112_p68250_w6_r13_pP.
Module C_XA_52944_cb62d_blk_w8_r15_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_cb62d_blk_w8_r15_L0.
Module C_XA_52944_cb62d_p682f0_w7_r14_pP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_10.C_XA_52944_cb62d_p682f0_w7_r14_pP.
Module C_ZLOOP_w4_r11_p3h682ecc7db_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_ZLOOP_w4_r11_p3h682ecc7db_L0.
Module C_ZLOOP_w4_r11_pP_L0_km160 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_ZLOOP_w4_r11_pP_L0_km160.
Module C_ZLOOP_w4_r11_pP_L0_km260 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_ZLOOP_w4_r11_pP_L0_km260.
Module C_ZLOOP_w5_r12_p3h6818cc68b_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_ZLOOP_w5_r12_p3h6818cc68b_L0.
Module C_ZLOOP_w5_r12_p3h6824cc132_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_16.C_ZLOOP_w5_r12_p3h6824cc132_L0.
Module C_ZLOOP_w5_r12_pP_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_ZLOOP_w5_r12_pP_L0.
Module C_ZLOOP_w5_r12_pv_L0_km160 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_ZLOOP_w5_r12_pv_L0_km160.
Module C_ZLOOP_w5_r12_pv_L0_km260 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_ZLOOP_w5_r12_pv_L0_km260.
Module C_ZLOOP_w6_r13_pv_L0 := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Cert.Ubs2UE.B_09.C_ZLOOP_w6_r13_pv_L0.

Module LibRunUbs_u_1.
Definition N : int := 118%uint63.
Record hyps (R : drun) (E0 : env) (K : TSet) : Prop := Hyps {
  h_pb : r_PB R (eb E0);
  h_ctabU : ctab_ok SEGS R T_Ubs2U.CONTRACTS;
  h_ctabUE : ctab_ok SEGS R T_Ubs2UE.CONTRACTS;
  h_ret9 : LNODE SEGS R N E0 K (t_st T_Ubs2F.R_LIBGEN_r9_RET) }.
Arguments Hyps R E0 K : clear implicits.
Lemma final9_st : t_st T_Ubs2U.T_FINAL_r9 = t_st T_Ubs2F.R_LIBGEN_r9_RET.
Proof. vm_compute. reflexivity. Qed.
Lemma h_ret9U (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_FINAL_r9).
Proof. rewrite final9_st. exact (@h_ret9 _ _ _ H). Qed.
Lemma lnode_family_nthT (R : drun) (E0 : env) (K : TSet) (HPB : r_PB R (eb E0)) : forall FAM i h T C P O cl,
  Forall (fmem_ok SEGS R N E0 K (heads FAM)) FAM -> nth_error FAM i = Some (FM h T C P O cl) -> LNODE SEGS R N E0 K (t_st T).
Proof. intros FAM i h T C P O cl HF Hi. exact (lnode_family_nth SEGS R N E0 K HPB FAM i (FM h T C P O cl) HF Hi). Qed.

Definition FAM_2 : list fmem := [
  FM 576%uint63 T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0 C_ZLOOP_w4_r11_p3h682ecc7db_L0.CTX C_ZLOOP_w4_r11_p3h682ecc7db_L0.PLAN C_ZLOOP_w4_r11_p3h682ecc7db_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)];
  FM 579%uint63 T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160 C_ZLOOP_w4_r11_pP_L0_km160.CTX C_ZLOOP_w4_r11_pP_L0_km160.PLAN C_ZLOOP_w4_r11_pP_L0_km160.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)];
  FM 580%uint63 T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260 C_ZLOOP_w4_r11_pP_L0_km260.CTX C_ZLOOP_w4_r11_pP_L0_km260.PLAN C_ZLOOP_w4_r11_pP_L0_km260.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)];
  FM 577%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0 C_ZLOOP_w5_r12_p3h6818cc68b_L0.CTX C_ZLOOP_w5_r12_p3h6818cc68b_L0.PLAN C_ZLOOP_w5_r12_p3h6818cc68b_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0)];
  FM 578%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0 C_ZLOOP_w5_r12_p3h6824cc132_L0.CTX C_ZLOOP_w5_r12_p3h6824cc132_L0.PLAN C_ZLOOP_w5_r12_p3h6824cc132_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)];
  FM 405%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0 C_ZLOOP_w5_r12_pP_L0.CTX C_ZLOOP_w5_r12_pP_L0.PLAN C_ZLOOP_w5_r12_pP_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)];
  FM 581%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160 C_ZLOOP_w5_r12_pv_L0_km160.CTX C_ZLOOP_w5_r12_pv_L0_km160.PLAN C_ZLOOP_w5_r12_pv_L0_km160.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)];
  FM 582%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260 C_ZLOOP_w5_r12_pv_L0_km260.CTX C_ZLOOP_w5_r12_pv_L0_km260.PLAN C_ZLOOP_w5_r12_pv_L0_km260.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)];
  FM 407%uint63 T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0 C_ZLOOP_w6_r13_pv_L0.CTX C_ZLOOP_w6_r13_pv_L0.PLAN C_ZLOOP_w6_r13_pv_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)]
  ].
Lemma FAMOK_2 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : Forall (fmem_ok SEGS R N E0 K (heads FAM_2)) FAM_2.
Proof.
  unfold FAM_2.
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w4_r11_p3h682ecc7db_L0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w4_r11_p3h682ecc7db_L0.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w4_r11_p3h682ecc7db_L0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w4_r11_pP_L0_km160.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w4_r11_pP_L0_km160.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w4_r11_pP_L0_km160.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w4_r11_pP_L0_km260.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w4_r11_pP_L0_km260.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w4_r11_pP_L0_km260.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w5_r12_p3h6818cc68b_L0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w5_r12_p3h6818cc68b_L0.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w5_r12_p3h6818cc68b_L0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w5_r12_p3h6824cc132_L0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w5_r12_p3h6824cc132_L0.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w5_r12_p3h6824cc132_L0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w5_r12_pP_L0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w5_r12_pP_L0.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w5_r12_pP_L0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w5_r12_pv_L0_km160.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w5_r12_pv_L0_km160.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w5_r12_pv_L0_km160.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w5_r12_pv_L0_km260.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w5_r12_pv_L0_km260.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w5_r12_pv_L0_km260.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_cons.
  { cbn [fmem_ok fm_id fm_tpl fm_ctx fm_plan fm_obls fm_cutl].
    split; [exact C_ZLOOP_w6_r13_pv_L0.WF|]. split; [exact ITAB_ok|]. split; [exact (contracts_ok_of SEGS R C_ZLOOP_w6_r13_pv_L0.CTX (@h_ctabUE _ _ _ H))|]. split; [vm_compute; reflexivity|].
    split; [exact C_ZLOOP_w6_r13_pv_L0.CHK|]. split; [constructor|].
    split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
    split; [reflexivity|]. split; [reflexivity|].
    apply Forall_cons; [right; cbn [snd]; exact (h_ret9U _ _ _ H)|]; apply Forall_cons; [left; split; [cbn [heads List.map fm_id fm_tpl In]; right; right; right; right; right; right; right; right; left; reflexivity | vm_compute; reflexivity]|]; apply Forall_nil. }
  apply Forall_nil.
Qed.
Lemma LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 0 576%uint63 T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0 C_ZLOOP_w4_r11_p3h682ecc7db_L0.CTX C_ZLOOP_w4_r11_p3h682ecc7db_L0.PLAN C_ZLOOP_w4_r11_p3h682ecc7db_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 1 579%uint63 T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160 C_ZLOOP_w4_r11_pP_L0_km160.CTX C_ZLOOP_w4_r11_pP_L0_km160.PLAN C_ZLOOP_w4_r11_pP_L0_km160.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 2 580%uint63 T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260 C_ZLOOP_w4_r11_pP_L0_km260.CTX C_ZLOOP_w4_r11_pP_L0_km260.PLAN C_ZLOOP_w4_r11_pP_L0_km260.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 3 577%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0 C_ZLOOP_w5_r12_p3h6818cc68b_L0.CTX C_ZLOOP_w5_r12_p3h6818cc68b_L0.PLAN C_ZLOOP_w5_r12_p3h6818cc68b_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 4 578%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0 C_ZLOOP_w5_r12_p3h6824cc132_L0.CTX C_ZLOOP_w5_r12_p3h6824cc132_L0.PLAN C_ZLOOP_w5_r12_p3h6824cc132_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w5_r12_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 5 405%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0 C_ZLOOP_w5_r12_pP_L0.CTX C_ZLOOP_w5_r12_pP_L0.PLAN C_ZLOOP_w5_r12_pP_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 6 581%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160 C_ZLOOP_w5_r12_pv_L0_km160.CTX C_ZLOOP_w5_r12_pv_L0_km160.PLAN C_ZLOOP_w5_r12_pv_L0_km160.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 7 582%uint63 T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260 C_ZLOOP_w5_r12_pv_L0_km260.CTX C_ZLOOP_w5_r12_pv_L0_km260.PLAN C_ZLOOP_w5_r12_pv_L0_km260.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_ZLOOP_w6_r13_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0).
Proof. exact (lnode_family_nthT R E0 K (@h_pb _ _ _ H) FAM_2 8 407%uint63 T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0 C_ZLOOP_w6_r13_pv_L0.CTX C_ZLOOP_w6_r13_pv_L0.PLAN C_ZLOOP_w6_r13_pv_L0.OBLS [(101%uint63, T_Ubs2UE.T_FINAL_r9); (407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] (FAMOK_2 R E0 K H) eq_refl). Qed.
Lemma LN_TUE_T_UW_52944_cb62d_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_cb62d_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_cb62d_w8_r15_pv_L0.CTX C_UW_52944_cb62d_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_cb62d_w8_r15_pv_L0) C_UW_52944_cb62d_w8_r15_pv_L0.OBLS [(582%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km260)] C_UW_52944_cb62d_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_cb62d_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_cb62d_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_cb62d_blk_w8_r15_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_cb62d_blk_w8_r15_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_cb62d_blk_w8_r15_L0.CTX C_XA_52944_cb62d_blk_w8_r15_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_cb62d_blk_w8_r15_L0) C_XA_52944_cb62d_blk_w8_r15_L0.OBLS [(557%uint63, T_Ubs2UE.T_UW_52944_cb62d_w8_r15_pv_L0)] C_XA_52944_cb62d_blk_w8_r15_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_cb62d_blk_w8_r15_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_cb62d_blk_w8_r15_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_cb62d_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_cb62d_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_cb62d_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_cb62d_w7_r14_pP_L0.CTX C_UW_52944_cb62d_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_cb62d_w7_r14_pP_L0) C_UW_52944_cb62d_w7_r14_pP_L0.OBLS [(580%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km260)] C_UW_52944_cb62d_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_cb62d_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_cb62d_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km260 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_cb62d_p682f0_w7_r14_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_cb62d_p682f0_w7_r14_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_cb62d_p682f0_w7_r14_pP.CTX C_XA_52944_cb62d_p682f0_w7_r14_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_cb62d_p682f0_w7_r14_pP) C_XA_52944_cb62d_p682f0_w7_r14_pP.OBLS [(556%uint63, T_Ubs2UE.T_UW_52944_cb62d_w7_r14_pP_L0)] C_XA_52944_cb62d_p682f0_w7_r14_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_cb62d_p682f0_w7_r14_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_cb62d_p682f0_w7_r14_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_cb62d_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.CTX C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1) C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.OBLS [(472%uint63, T_Ubs2UE.T_XA_52944_cb62d_blk_w8_r15_L0); (473%uint63, T_Ubs2UE.T_XA_52944_cb62d_p682f0_w7_r14_pP)] C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_cb62d_blk_w8_r15_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_cb62d_p682f0_w7_r14_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_2037c_48285_w8_r15_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_2037c_48285_w8_r15_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_2037c_48285_w8_r15_pv_L0.CTX C_UW_2037c_48285_w8_r15_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_2037c_48285_w8_r15_pv_L0) C_UW_2037c_48285_w8_r15_pv_L0.OBLS [(407%uint63, T_Ubs2UE.T_ZLOOP_w6_r13_pv_L0)] C_UW_2037c_48285_w8_r15_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_2037c_48285_w8_r15_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_2037c_48285_w8_r15_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w6_r13_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_2037c_48285_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_2037c_48285_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_2037c_48285_blk_w7_r14_L0.CTX C_XA_2037c_48285_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_2037c_48285_blk_w7_r14_L0) C_XA_2037c_48285_blk_w7_r14_L0.OBLS [(232%uint63, T_Ubs2UE.T_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1); (277%uint63, T_Ubs2UE.T_UW_2037c_48285_w8_r15_pv_L0)] C_XA_2037c_48285_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_2037c_48285_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_2037c_48285_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_2037c_48285_blk_w7_r14_L0_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_2037c_48285_w8_r15_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_7e112_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_7e112_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_7e112_w7_r14_pP_L0.CTX C_UW_52944_7e112_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_7e112_w7_r14_pP_L0) C_UW_52944_7e112_w7_r14_pP_L0.OBLS [(577%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6818cc68b_L0); (578%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_p3h6824cc132_L0)] C_UW_52944_7e112_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_7e112_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_7e112_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6818cc68b_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_p3h6824cc132_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_7e112_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_7e112_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_7e112_blk_w7_r14_L0.CTX C_XA_52944_7e112_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_7e112_blk_w7_r14_L0) C_XA_52944_7e112_blk_w7_r14_L0.OBLS [(531%uint63, T_Ubs2UE.T_UW_52944_7e112_w7_r14_pP_L0)] C_XA_52944_7e112_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_7e112_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_7e112_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_7e112_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_7e112_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_7e112_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_7e112_w6_r13_pP_L0.CTX C_UW_52944_7e112_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_7e112_w6_r13_pP_L0) C_UW_52944_7e112_w6_r13_pP_L0.OBLS [(576%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_p3h682ecc7db_L0)] C_UW_52944_7e112_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_7e112_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_7e112_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_p3h682ecc7db_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_7e112_p68250_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_7e112_p68250_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_7e112_p68250_w6_r13_pP.CTX C_XA_52944_7e112_p68250_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_7e112_p68250_w6_r13_pP) C_XA_52944_7e112_p68250_w6_r13_pP.OBLS [(530%uint63, T_Ubs2UE.T_UW_52944_7e112_w6_r13_pP_L0)] C_XA_52944_7e112_p68250_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_7e112_p68250_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_7e112_p68250_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_7e112_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.CTX C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.PLAN (t_st T_Ubs2UE.T_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1) C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.OBLS [(446%uint63, T_Ubs2UE.T_XA_52944_7e112_blk_w7_r14_L0); (447%uint63, T_Ubs2UE.T_XA_52944_7e112_p68250_w6_r13_pP)] C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.WF ITAB_ok (contracts_ok_of SEGS R C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.CTX (@h_ctabUE _ _ _ H)) C_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_7e112_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_7e112_p68250_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_2037c_48285_w7_r14_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_2037c_48285_w7_r14_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_2037c_48285_w7_r14_pP_L0.CTX C_UW_2037c_48285_w7_r14_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_2037c_48285_w7_r14_pP_L0) C_UW_2037c_48285_w7_r14_pP_L0.OBLS [(405%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pP_L0)] C_UW_2037c_48285_w7_r14_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_2037c_48285_w7_r14_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_2037c_48285_w7_r14_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_2037c_48285_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_2037c_48285_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_2037c_48285_p682f0_w6_r13_pP.CTX C_XA_2037c_48285_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_2037c_48285_p682f0_w6_r13_pP) C_XA_2037c_48285_p682f0_w6_r13_pP.OBLS [(233%uint63, T_Ubs2UE.T_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1); (276%uint63, T_Ubs2UE.T_UW_2037c_48285_w7_r14_pP_L0)] C_XA_2037c_48285_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_2037c_48285_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_2037c_48285_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_THROW_n52944_XA_2037c_48285_p682f0_w6_r13_pP_1 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_UW_2037c_48285_w7_r14_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.CTX C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.PLAN (t_st T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22) C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.OBLS [(104%uint63, T_Ubs2UE.T_XA_2037c_48285_blk_w7_r14_L0); (105%uint63, T_Ubs2UE.T_XA_2037c_48285_p682f0_w6_r13_pP)] C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.WF ITAB_ok (contracts_ok_of SEGS R C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.CTX (@h_ctabUE _ _ _ H)) C_EH_2037c_s10_m5_w6_r13_pv_L0_fcc6b22.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_2037c_48285_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_2037c_48285_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.CTX C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.PLAN (t_st T_Ubs2U.T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22) C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.OBLS [(139%uint63, T_Ubs2U.T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22)] C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.CTX (@h_ctabU _ _ _ H)) C_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_2037c_s10_m5_w6_r13_pv_L0_fcc6b22 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_EXECRET_rc0_m1_n14_w0111234 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_EXECRET_rc0_m1_n14_w0111234).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EXECRET_rc0_m1_n14_w0111234.CTX C_EXECRET_rc0_m1_n14_w0111234.PLAN (t_st T_Ubs2U.T_EXECRET_rc0_m1_n14_w0111234) C_EXECRET_rc0_m1_n14_w0111234.OBLS [(136%uint63, T_Ubs2U.T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22)] C_EXECRET_rc0_m1_n14_w0111234.WF ITAB_ok (contracts_ok_of SEGS R C_EXECRET_rc0_m1_n14_w0111234.CTX (@h_ctabU _ _ _ H)) C_EXECRET_rc0_m1_n14_w0111234.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_PRETHROW_2037c_s10_m1_w7_r14_pv_L0_fcc6b22 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_4a174_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_4a174_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_4a174_w7_r14_pv_L0.CTX C_UW_52944_4a174_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_4a174_w7_r14_pv_L0) C_UW_52944_4a174_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_52944_4a174_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_4a174_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_4a174_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_4a174_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_4a174_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_4a174_blk_w7_r14_L0.CTX C_XA_52944_4a174_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_52944_4a174_blk_w7_r14_L0) C_XA_52944_4a174_blk_w7_r14_L0.OBLS [(377%uint63, T_Ubs2UE.T_UW_52944_4a174_w7_r14_pv_L0)] C_XA_52944_4a174_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_4a174_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_4a174_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_4a174_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_52944_4a174_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_52944_4a174_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_52944_4a174_w6_r13_pP_L0.CTX C_UW_52944_4a174_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_52944_4a174_w6_r13_pP_L0) C_UW_52944_4a174_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_52944_4a174_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_52944_4a174_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_52944_4a174_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_52944_4a174_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_52944_4a174_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_52944_4a174_p682f0_w6_r13_pP.CTX C_XA_52944_4a174_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_52944_4a174_p682f0_w6_r13_pP) C_XA_52944_4a174_p682f0_w6_r13_pP.OBLS [(376%uint63, T_Ubs2UE.T_UW_52944_4a174_w6_r13_pP_L0)] C_XA_52944_4a174_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_52944_4a174_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_52944_4a174_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_52944_4a174_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.CTX C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.PLAN (t_st T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e) C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.OBLS [(204%uint63, T_Ubs2UE.T_XA_52944_4a174_blk_w7_r14_L0); (205%uint63, T_Ubs2UE.T_XA_52944_4a174_p682f0_w6_r13_pP)] C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.WF ITAB_ok (contracts_ok_of SEGS R C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.CTX (@h_ctabUE _ _ _ H)) C_EH_52944_s8_m5_w6_r13_pv_L0_f2b130e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_52944_4a174_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_52944_4a174_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.CTX C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.PLAN (t_st T_Ubs2U.T_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e) C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.OBLS [(229%uint63, T_Ubs2U.T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e)] C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_52944_s8_m3_w6_r13_pv_L0_f2b130e.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_52944_s8_m5_w6_r13_pv_L0_f2b130e _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_0c366_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_0c366_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_0c366_w7_r14_pv_L0.CTX C_UW_236d8_0c366_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_0c366_w7_r14_pv_L0) C_UW_236d8_0c366_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_0c366_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_0c366_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_0c366_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_0c366_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_0c366_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_0c366_blk_w7_r14_L0.CTX C_XA_236d8_0c366_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_0c366_blk_w7_r14_L0) C_XA_236d8_0c366_blk_w7_r14_L0.OBLS [(337%uint63, T_Ubs2UE.T_UW_236d8_0c366_w7_r14_pv_L0)] C_XA_236d8_0c366_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_0c366_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_0c366_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_0c366_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_0c366_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_0c366_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_0c366_w6_r13_pP_L0.CTX C_UW_236d8_0c366_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_0c366_w6_r13_pP_L0) C_UW_236d8_0c366_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_0c366_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_0c366_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_0c366_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_0c366_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_0c366_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_0c366_p682f0_w6_r13_pP.CTX C_XA_236d8_0c366_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_0c366_p682f0_w6_r13_pP) C_XA_236d8_0c366_p682f0_w6_r13_pP.OBLS [(336%uint63, T_Ubs2UE.T_UW_236d8_0c366_w6_r13_pP_L0)] C_XA_236d8_0c366_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_0c366_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_0c366_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_0c366_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6) C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.OBLS [(164%uint63, T_Ubs2UE.T_XA_236d8_0c366_blk_w7_r14_L0); (165%uint63, T_Ubs2UE.T_XA_236d8_0c366_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_fcadae6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_0c366_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_0c366_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.OBLS [(298%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_fcadae6.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_fcadae6 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_52706_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_52706_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_52706_w7_r14_pv_L0.CTX C_UW_236d8_52706_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_52706_w7_r14_pv_L0) C_UW_236d8_52706_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_52706_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_52706_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_52706_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_52706_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_52706_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_52706_blk_w7_r14_L0.CTX C_XA_236d8_52706_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_52706_blk_w7_r14_L0) C_XA_236d8_52706_blk_w7_r14_L0.OBLS [(347%uint63, T_Ubs2UE.T_UW_236d8_52706_w7_r14_pv_L0)] C_XA_236d8_52706_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_52706_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_52706_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_52706_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_52706_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_52706_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_52706_w6_r13_pP_L0.CTX C_UW_236d8_52706_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_52706_w6_r13_pP_L0) C_UW_236d8_52706_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_52706_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_52706_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_52706_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_52706_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_52706_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_52706_p682f0_w6_r13_pP.CTX C_XA_236d8_52706_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_52706_p682f0_w6_r13_pP) C_XA_236d8_52706_p682f0_w6_r13_pP.OBLS [(346%uint63, T_Ubs2UE.T_UW_236d8_52706_w6_r13_pP_L0)] C_XA_236d8_52706_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_52706_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_52706_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_52706_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.CTX C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.PLAN (t_st T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66) C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.OBLS [(174%uint63, T_Ubs2UE.T_XA_236d8_52706_blk_w7_r14_L0); (175%uint63, T_Ubs2UE.T_XA_236d8_52706_p682f0_w6_r13_pP)] C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.WF ITAB_ok (contracts_ok_of SEGS R C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.CTX (@h_ctabUE _ _ _ H)) C_EH_236d8_s8_m5_w6_r13_pv_L0_f796e66.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_XA_236d8_52706_blk_w7_r14_L0 _ _ _ H)|]; apply Forall_cons; [exact (LN_TUE_T_XA_236d8_52706_p682f0_w6_r13_pP _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TU_T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.CTX C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.PLAN (t_st T_Ubs2U.T_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.OBLS [(299%uint63, T_Ubs2U.T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66)] C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.WF ITAB_ok (contracts_ok_of SEGS R C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.CTX (@h_ctabU _ _ _ H)) C_PRETHROWPK_236d8_s8_m3_w6_r13_pv_L0_f796e66.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TU_T_THROW_236d8_s8_m5_w6_r13_pv_L0_f796e66 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_c92f2_w7_r14_pv_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_c92f2_w7_r14_pv_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_c92f2_w7_r14_pv_L0.CTX C_UW_236d8_c92f2_w7_r14_pv_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_c92f2_w7_r14_pv_L0) C_UW_236d8_c92f2_w7_r14_pv_L0.OBLS [(581%uint63, T_Ubs2UE.T_ZLOOP_w5_r12_pv_L0_km160)] C_UW_236d8_c92f2_w7_r14_pv_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_c92f2_w7_r14_pv_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_c92f2_w7_r14_pv_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w5_r12_pv_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_c92f2_blk_w7_r14_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_c92f2_blk_w7_r14_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_c92f2_blk_w7_r14_L0.CTX C_XA_236d8_c92f2_blk_w7_r14_L0.PLAN (t_st T_Ubs2UE.T_XA_236d8_c92f2_blk_w7_r14_L0) C_XA_236d8_c92f2_blk_w7_r14_L0.OBLS [(361%uint63, T_Ubs2UE.T_UW_236d8_c92f2_w7_r14_pv_L0)] C_XA_236d8_c92f2_blk_w7_r14_L0.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_c92f2_blk_w7_r14_L0.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_c92f2_blk_w7_r14_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_c92f2_w7_r14_pv_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_UW_236d8_c92f2_w6_r13_pP_L0 (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_UW_236d8_c92f2_w6_r13_pP_L0).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_UW_236d8_c92f2_w6_r13_pP_L0.CTX C_UW_236d8_c92f2_w6_r13_pP_L0.PLAN (t_st T_Ubs2UE.T_UW_236d8_c92f2_w6_r13_pP_L0) C_UW_236d8_c92f2_w6_r13_pP_L0.OBLS [(579%uint63, T_Ubs2UE.T_ZLOOP_w4_r11_pP_L0_km160)] C_UW_236d8_c92f2_w6_r13_pP_L0.WF ITAB_ok (contracts_ok_of SEGS R C_UW_236d8_c92f2_w6_r13_pP_L0.CTX (@h_ctabUE _ _ _ H)) C_UW_236d8_c92f2_w6_r13_pP_L0.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_ZLOOP_w4_r11_pP_L0_km160 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
Lemma LN_TUE_T_XA_236d8_c92f2_p682f0_w6_r13_pP (R : drun) (E0 : env) (K : TSet) (H : hyps R E0 K) : LNODE SEGS R N E0 K (t_st T_Ubs2UE.T_XA_236d8_c92f2_p682f0_w6_r13_pP).
Proof.
  apply (lnode_cert SEGS R N E0 K (@h_pb _ _ _ H) C_XA_236d8_c92f2_p682f0_w6_r13_pP.CTX C_XA_236d8_c92f2_p682f0_w6_r13_pP.PLAN (t_st T_Ubs2UE.T_XA_236d8_c92f2_p682f0_w6_r13_pP) C_XA_236d8_c92f2_p682f0_w6_r13_pP.OBLS [(360%uint63, T_Ubs2UE.T_UW_236d8_c92f2_w6_r13_pP_L0)] C_XA_236d8_c92f2_p682f0_w6_r13_pP.WF ITAB_ok (contracts_ok_of SEGS R C_XA_236d8_c92f2_p682f0_w6_r13_pP.CTX (@h_ctabUE _ _ _ H)) C_XA_236d8_c92f2_p682f0_w6_r13_pP.CHK
           ltac:(constructor) eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) eq_refl ltac:(apply Forall_cons; [exact (LN_TUE_T_UW_236d8_c92f2_w6_r13_pP_L0 _ _ _ H)|]; apply Forall_nil) eq_refl).
Qed.
End LibRunUbs_u_1.
