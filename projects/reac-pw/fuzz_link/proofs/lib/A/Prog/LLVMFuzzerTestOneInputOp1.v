(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module paths and module names changed; 69 of its 110 lines of code are new or changed and 1291 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A: op_write, the arm of the 48-operation loop at operation byte mod 6 = 1
   (entry +0x8e4 = 0x830b8), from the arm's entry cut to the loop tail (+0x1110 = 0x838e4).
   Offsets from 0x827d4; listing (internal path) (internal record, sha256 e84d6f0c6974).

     lf_op1 : forall POST i, 0 <= i <= 47 ->
       FROM POST (lf_tail_inv i) -> FROM POST (lf_arm_inv 1 i)

   The pieces, each a lemma of its file, composed here:
     +0x8e4 .. +0xffc  the name selector (Op1S.v w_sel, Sel.v's shared join)
     +0xffc .. +0x1014 text_of(&cursor, &s1+0x130) at 0x837d8, kernel(&cursor) at 0x837e4 (Op1A.v w_tk)
     +0x1014 .. +0x1078 the five counter stores and g_nl.opened into s4 (Op1B.v w_kb)
     +0x1078 model_write (0x83858, Op1C.v w_bm); +0x1088 reac_link_alias_write (0x83868, Op1D.v w_ma)
     +0x1098 check_socket (0x83870, Op1E.v w_as); +0x10a0 the name tests and the strlen wrapper (0x83894, Op1F.v
     w_sl); +0x10c4 the 0xff bound and index_of (0x838a4, Op1E.v w_lx); +0x10d4 index_of's test (Op1E.v w_xj);
     +0x10d8 check_refused (0x838b8, Op1E.v w_jr); +0x10e8 check_write (0x838c4, Op1G.v w_jq);
     +0x10f4 check_requests (0x838d0), free of the text block (0x838d8), the reloads (Op1G.v w_qt).
   text_of's read-only premise (W3) is discharged here by Txo.v lf_txo_ro.

   Proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YI00 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YO09 YGwildCount YImgTop.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFile AMemFileSink LinkWildRoom.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PcapRelro YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA LinkWalkZsh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import text_of_c kernel_c model_write_c index_of_c reac_link_alias_write_c nl_talk_c check_socket_c check_refused_c check_write_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpre.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKeep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputLp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMb.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmR.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3K.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputArmH.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputMdl.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputNm.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputKpost.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1C.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1D.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1E.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp3Lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputFree.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkStrS YC88.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputTxo.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputOp1S LLVMFuzzerTestOneInputOp1A
  LLVMFuzzerTestOneInputOp1B LLVMFuzzerTestOneInputOp1C LLVMFuzzerTestOneInputOp1D LLVMFuzzerTestOneInputOp1E
  LLVMFuzzerTestOneInputOp1F LLVMFuzzerTestOneInputOp1G.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.
(* the image instance's facts *)
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
(* the meter's triviality (the image instance's ameter_triv) *)
Hypothesis MT_OK : forall S m, mo_ok MT S m.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
(* the callees' contracts, each as its owner proves it *)
Hypothesis TXO_TR : text_of_traces B.
Hypothesis TXO_C : forall fy : YK11.FPState, text_of_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B MT LF_CTX.
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ALIAS_WRITE : forall fy : YK11.FPState,
  @reac_link_alias_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CSOCK : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ASTRLEN : forall fy : YK11.FPState,
  @RtString.astrlen_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_strlen).
Hypothesis INDEX_OF : forall fy : YK11.FPState, @index_of_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREF : forall fy : YK11.FPState, @check_refused_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CWRITE : forall fy : YK11.FPState, @check_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREQ : forall fy : YK11.FPState, @check_requests_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
(* the allocator's free rules and the free sites' traces (open item W1) *)
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

Ltac wstep L := eapply L; try eassumption; try exact (lf_txo_ro B HSEGS TB).

Lemma lf_op1 : forall POST i, 0 <= i <= 47 ->
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP 1 i).
Proof.
  intros POST i Hi HT.
  wstep w_sel. wstep w_tk. wstep w_kb. wstep w_bm. wstep w_ma. wstep w_as. wstep w_sl.
  - wstep w_jr. wstep w_jq. wstep w_qt.
  - wstep w_lx.
    + wstep w_jr. wstep w_jq. wstep w_qt.
    + wstep w_xj.
      * wstep w_jq. wstep w_qt.
      * wstep w_jr. wstep w_jq. wstep w_qt.
Qed.

End a.
