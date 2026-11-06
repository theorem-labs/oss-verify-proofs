(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 48 of its 86 lines of code are new or changed and 1294 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_read arm (operation byte mod 6 = 0): the arm from its
   entry lf_op_pc 0 = +0x608 to the loop tail LF_tail = +0x1110, composed from its segments
   (listing (internal path) (internal record, sha256 e84d6f0c6974)):
     +0x608 .. +0xd14  the name selector                 Op0S.v r_sel
     +0xd14 .. +0xdac  the two size bytes, mod 40         Op0C.v r_sizes
     +0xdac .. +0xdb4  kernel(in)                         Op0K.v r_kcall
     +0xdb4 .. +0xe1c  model_begin(m)                     Op0B.v r_begin
     +0xe1c .. +0xe34  text_buf(kc), text_buf(ac)         Op0T.v r_tbufs
     +0xe34 .. +0xe90  wk, wa in scope and zeroed, opened Op0Z.v r_zero
     +0xe90 .. +0xebc  model_read                         Op0R.v r_mread
     +0xebc .. +0xed8  reac_link_alias_read               Op0A.v r_aread
     +0xed8 .. +0xf1c  check_socket, the name, index_of, check_refused   Op0Q.v r_checks
     +0xf1c .. +0xf7c  check_bounds x2, check_read, check_requests       Op0V.v r_verify
     +0xf7c .. +0x1110 the two frees, the frame shadow restored, LF_tail Op0F.v r_fin
   The cuts between them are Op0Cut.v's (and Sel.v sel_join at +0xd14, Op0V.v r_v at +0xf7c).
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c text_buf_c model_read_c
  reac_link_alias_read_c check_socket_c check_refused_c index_of_c check_bounds_c check_read_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs
  LLVMFuzzerTestOneInputFree LLVMFuzzerTestOneInputTxa LLVMFuzzerTestOneInputSel LLVMFuzzerTestOneInputOp0Cut
  LLVMFuzzerTestOneInputOp0K LLVMFuzzerTestOneInputOp0B LLVMFuzzerTestOneInputOp0T LLVMFuzzerTestOneInputOp0Z
  LLVMFuzzerTestOneInputOp0R LLVMFuzzerTestOneInputOp0A LLVMFuzzerTestOneInputOp0Q LLVMFuzzerTestOneInputOp0V
  LLVMFuzzerTestOneInputOp0F LLVMFuzzerTestOneInputOp0C LLVMFuzzerTestOneInputOp0S.
Import ListNotations.
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
Hypothesis LV : LinkVals (L := link_listing).
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TB : PcapSyms B.
Hypothesis HSEGS : pa_segs = tfibsegs.
Hypothesis MT_LE : forall S S' m, mo_le MT S S' m.
Hypothesis MT_OK : forall S m, mo_ok MT S m.
(* the callees, as proved (the *_c.v contracts), the allocator's free rules and the
   free sites' traces (Free.v, open item W1), text_buf's sites' traces, and checked_memset (lib/A/AE2r.v
   asan_memset_realizes; the entry's LLVMFuzzerTestOneInputEntry.v lf_memset_intrin gives it) *)
Hypothesis KERNEL : forall fy : YK11.FPState, @kernel_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis TXB_C : forall fy : YK11.FPState, text_buf_acontract (fx := fy) SK SEGS PCAP_RLO PCAP_RHI B MT LF_CTX.
Hypothesis TXB_TR : text_buf_traces B LF_CTX.
Hypothesis AMSET : forall fy : YK11.FPState, aintrin_realizes (fx := fy) pa_segs B OSet 0x53214.
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ALIAS_READ : forall fy : YK11.FPState,
  @reac_link_alias_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CSOCK : forall fy : YK11.FPState, @check_socket_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREF : forall fy : YK11.FPState, @check_refused_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis INDEX_OF : forall fy : YK11.FPState, @index_of_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CBND : forall fy : YK11.FPState, @check_bounds_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREAD : forall fy : YK11.FPState, @check_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis CREQ : forall fy : YK11.FPState, @check_requests_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis AFREE4W : forall fy : YK11.FPState, afree04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis AFREENULL4W : forall fy : YK11.FPState, afree_null04_rule_w (fx := fy) SK SEGS B MT.
Hypothesis LF_TRACE_FREE : lf_trace_free B.

Local Notation FROM := (@lf_from fx rc SK PI B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the arm: from its entry (lf_arm_inv at op 0) to the loop tail (lf_tail_inv) *)
Lemma lf_op0 : forall POST i, 0 <= i <= 47 ->
  FROM POST (lf_tail_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  FROM POST (lf_arm_inv B MT MS la_nul LF_MO_SET LF_MO_OP 0 i).
Proof.
  intros POST i Hi HT.
  apply LLVMFuzzerTestOneInputOp0S.r_sel; try assumption.
  apply r_sizes; try assumption.
  apply r_kcall; try assumption.
  apply r_begin; try assumption.
  apply r_tbufs; try assumption.
  apply r_zero; try assumption.
  apply r_mread; try assumption.
  apply r_aread; try assumption.
  apply r_checks; try assumption.
  apply r_verify; try assumption.
  apply r_fin; assumption.
Qed.

End a.
