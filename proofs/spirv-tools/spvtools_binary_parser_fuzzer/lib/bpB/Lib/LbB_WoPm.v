(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_Call LbB_Bridge.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_SR LbB_WoGen LbB_WoDefs LbB_WoKit LbB_PiStmt LbB_PiInit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PiStmt LbB_HdrGet LbB_DiagStmt LbB_WoBP.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_WoBPW LbB_PmLWo LbB_PmHTW LbB_PmD4_1 LbB_PmMag.
Import ListNotations.

#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section WoPm.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Hypothesis PI : parse_inst_stmtB H LINV_P5.
  Hypothesis HTR : pm_tr_ok H.
  Hypothesis HG : hdr_get_stmt.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV_P5 ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV_P5 ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV_P5 ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV_P5 ds_repA.
  Hypothesis HU32 : put_u32_stmtA H LINV_P5 ds_repA.
  Hypothesis HU64 : put_u64_stmtA H LINV_P5 ds_repA.

  Lemma wpm_dtr : pm_tr_ok H -> ds_tr_ok H.
  Proof. intros T. unfold pm_tr_ok, PM_DEL_RAS in T. exact (Forall_inv T). Qed.

  Lemma wpm_bp : forall e ff fp Q mo0, bp_kwcf H e ff fp Q mo0 -> bp_k480 H e ff fp Q mo0.
  Proof.
    intros e ff fp Q mo0 K.
    assert (KM : bp_kmagf H e ff fp Q mo0) by (eapply bp_kmagf_of_kwcf; eassumption).
    assert (KL : bp_klexit H e ff fp Q mo0) by (eapply bp_klexit_of_kmagf; eassumption).
    assert (KO : bp_kloop H e ff fp Q mo0) by (eapply bp_loop_wo; eassumption).
    assert (KD : bp_kd4 H e ff fp Q mo0) by (eapply (pm_d4 H HHbp ds_repA DSL (wpm_dtr HTR)); eassumption).
    assert (KG : bp_kgood H e ff fp Q mo0) by (eapply bp_kgood_of; eassumption).
    assert (KH : bp_khdr H e ff fp Q mo0) by (eapply pm_hdr; eassumption).
    eapply bp_k480_of_khdr; eassumption.
  Qed.
End WoPm.
