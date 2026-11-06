(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 70 of its 111 lines of code are new or changed and 1291 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A (fuzz_link.asan, the PUBLISHED pin, sha256 059dae63e07c...): op_mark,
   operation byte mod 6 = 2, entry +0x6a8 (listing (internal path)
   (internal record, sha256 e84d6f0c6974)). The arm's segments, each proved in its file:
     Op2E.v o2_sel   +0x6a8 .. +0xad4   the name selector and the kernel call                  ARM 2 <- o2_k_inv
     Op2B.v o2_kb    +0xad4 .. +0xb54   model_begin, the NULL / empty-name tests               o2_k_inv <- o2_q_inv, o2_n_inv
     Op2R.v o2_rd    +0xb54 .. +0xc04   the frame object into scope, model_read                o2_n_inv <- o2_r_inv
     Op2D.v o2_dc    +0xc04 .. +0x1120  model_read's answer, model_decide                      o2_r_inv <- o2_u_inv, o2_d_inv
     Op2V.v o2_dv    +0x112c ..         the verdict, model_write or the bcmp wrapper           o2_d_inv <- o2_u_inv, o2_w_inv, o2_b_inv
     Op2X.v o2_wr / o2_br               their answers                                          o2_w_inv / o2_b_inv <- o2_u_inv, o2_m_inv
     Op2M.v o2_mh    +0x1178            the inlined remember: the count                        o2_m_inv <- o2_a_inv, o2_l_inv 0
     Op2L.v o2_loop  +0x1180 ..         the strcmp loop over the marks                         o2_l_inv j <- o2_u_inv, o2_a_inv
     Op2A.v o2_ap    +0x11b4 .. +0x11fc the append, snprintf at 0x839c4                        o2_a_inv <- o2_u_inv
     Op2U.v o2_un    +0xc0c .. +0xc9c   the frame object out of scope                          o2_u_inv <- o2_q_inv
     Op2QM.v o2_qm   +0xc9c .. +0xcac   mark_quietly at 0x8347c                                o2_q_inv <- o2_y_inv +0xcac
     Op2Y.v o2y_exit +0xcac .. +0x1110  check_socket, check_mark, check_marks, check_requests  o2_y_inv +0xcac <- TAIL
   lf_op2 : the walk from the arm's cut to the loop tail's cut, at the same operation index i.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalk LinkWalkSide BoxBase LinkWalkPi.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputKeep LLVMFuzzerTestOneInputKpre LLVMFuzzerTestOneInputArmW LLVMFuzzerTestOneInputLp
  LLVMFuzzerTestOneInputDec LLVMFuzzerTestOneInputArmR LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3Cut
  LLVMFuzzerTestOneInputKpost LLVMFuzzerTestOneInputMb LLVMFuzzerTestOneInputMdl LLVMFuzzerTestOneInputOp3K
  LLVMFuzzerTestOneInputArmK.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c model_decide_c index_of_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputMq
  LLVMFuzzerTestOneInputOp2Lib LLVMFuzzerTestOneInputOp2Cut LLVMFuzzerTestOneInputOp2Nm LLVMFuzzerTestOneInputOp5
  LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C LLVMFuzzerTestOneInputOp2R LLVMFuzzerTestOneInputDec
  LLVMFuzzerTestOneInputOp3Lib LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp2D LLVMFuzzerTestOneInputOp2Nm
  LLVMFuzzerTestOneInputOp2V LLVMFuzzerTestOneInputOp2Ml.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkPfPiece LinkSnpDef LinkSnpJ.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputSnp rememberPost
  LLVMFuzzerTestOneInputOp2M LLVMFuzzerTestOneInputOp2X LinkWalkStrArg rememberCalls LLVMFuzzerTestOneInputOp2L
  LLVMFuzzerTestOneInputOp3K LLVMFuzzerTestOneInputOp3X.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import mark_quietly_c check_write_c check_mark_c
  check_socket_c check_marks_c check_requests_c LLVMFuzzerTestOneInputMqCall LLVMFuzzerTestOneInputOp2K
  LLVMFuzzerTestOneInputOp2E LLVMFuzzerTestOneInputOp2B LLVMFuzzerTestOneInputOp2U LLVMFuzzerTestOneInputOp2A
  LLVMFuzzerTestOneInputOp2Y LLVMFuzzerTestOneInputOp2QM.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.

Section b.
Context {PI : PAImg link_listing}.

Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variable MS : amemfile_syms.
Variable la_nul : Z.
Variable LF_CTX : list (list Z).
Variables LF_MO_SET LF_MO_OP LF_MO_END : Z.

#[local] Abbreviation FROM POST GI :=
  (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END POST GI).
#[local] Abbreviation ARM op i := (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP op i).
#[local] Abbreviation TAIL i := (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i).

Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* the callees, each as its lane proves it *)
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MDC : forall fy : YK11.FPState, model_decide_acontract (fx := fy) SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ABCMP : forall fy : YK11.FPState, @abcmp_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_bcmp).
Hypothesis STRCMP : forall fy : YK11.FPState,
  @RtString.astrcmp_realizes fy rc pa_segs B (pa_sigma LS___interceptor_trampoline_strcmp).
Hypothesis SNP : forall fy : YK11.FPState,
  @asnprintf_link_realizes fy rc pa_segs B PCAP_RLO PCAP_RHI LA_W_SNPRINTF.
Hypothesis MQO : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_open fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B MT (mo_malloc MT AMF_BLOCK) LF_CTX
    (fun _ => True) (mq_ledpost B).
Hypothesis MQA : forall fx0 : YK11.FPState,
  @mark_quietly_acontract_again fx0 rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CS : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CM : forall fy : YK11.FPState, @check_mark_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CMK : forall fy : YK11.FPState, @check_marks_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CR : forall fy : YK11.FPState, @check_requests_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.

Lemma lf_op2 : forall POST i, 0 <= i <= 47 -> FROM POST (TAIL i) -> FROM POST (ARM 2 i).
Proof.
  intros POST i Hi H.
  assert (HY : FROM POST (o2_y_inv B MT MS la_nul LF_MO_SET LF_MO_OP (AF_LLVMFuzzerTestOneInput + 0xcac) 10%bv i))
    by (apply o2y_exit; assumption).
  assert (HQ : FROM POST (o2_q_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_qm; assumption).
  assert (HU : FROM POST (o2_u_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_un; assumption).
  assert (HA : FROM POST (o2_a_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_ap; assumption).
  assert (HL : FROM POST (o2_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i 0)) by (apply o2_loop; assumption).
  assert (HM : FROM POST (o2_m_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_mh; assumption).
  assert (HW : FROM POST (o2_w_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_wr; assumption).
  assert (HBv : FROM POST (o2_b_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_br; assumption).
  assert (HD : FROM POST (o2_d_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_dv; assumption).
  assert (HR : FROM POST (o2_r_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_dc; assumption).
  assert (HN : FROM POST (o2_n_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_rd; assumption).
  assert (HK : FROM POST (o2_k_inv B MT MS la_nul LF_MO_SET LF_MO_OP i)) by (apply o2_kb; assumption).
  apply o2_sel; assumption.
Qed.

End b.
End a.
