(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module paths, module names and numbers changed; 1072 of its 1332 lines of code are new or changed and 1047 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/LLVMFuzzerTestOneInputEntry.v, with its module names changed; 42 of its 87 lines of code are new or changed and 1287 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput on image A, the op_unmark arm: the per-mark loop (+0x76c .. +0x8d0) by induction on the
   marks left: from the loop head at any mark j to the exit cut u_x_inv.
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
  LLVMFuzzerTestOneInputArmK LLVMFuzzerTestOneInputOp3B LLVMFuzzerTestOneInputOp3C
  LLVMFuzzerTestOneInputOp3W LLVMFuzzerTestOneInputOp3T.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c model_write_c LinkWalkBcmp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_spec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.


Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
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
Hypothesis MODEL_READ : forall fy : YK11.FPState, @model_read_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis MODEL_WRITE : forall fy : YK11.FPState, @model_write_acontract fy rc SK pa_segs PCAP_RLO PCAP_RHI B.
Hypothesis ABCMP : forall fy : YK11.FPState, @abcmp_realizes fy rc SEGS B (pa_sigma LS___interceptor_trampoline_bcmp).

Local Notation FROM := (lf_from SK B MT XM_LIB XN_LIB MS la_nul LF_CTX LF_MO_SET LF_MO_OP LF_MO_END).

(* the loop head holds only below 32 marks *)
Lemma u_l_bound : forall POST i j, 32 <= j -> FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i j Hj32 cx fy fp k2 ly3 S3 W3 ms3 md3 HB Hfx HJ Hfr HL.
  destruct HL as (md & mk & P & N & kbs & mbs & gbs & T3 & _ & _ & _ & _ & HU & Hj & _).
  pose proof HU as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hdat & _).
  pose proof Hdat as (_ & _ & _ & _ & _ & _ & _ & Dmwf & _).
  pose proof Dmwf as (_ & _ & _ & _ & _ & (Wnm & _)). unfold MARKS_MAX in Wnm. lia.
Qed.

Lemma u_loop : forall POST i,
  FROM POST (u_x_inv B MT MS la_nul LF_MO_SET LF_MO_OP i) ->
  forall j, FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j).
Proof.
  intros POST i HX.
  assert (G : forall n j, (Z.to_nat (32 - j) <= n)%nat -> FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j)).
  { induction n as [|n IH]; intros j Hn.
    - apply u_l_bound. lia.
    - destruct (Z_lt_le_dec j 32) as [Hj | Hj]; [|apply u_l_bound; exact Hj].
      assert (IHj : FROM POST (u_l_inv B MT MS la_nul LF_MO_SET LF_MO_OP i (j + 1))) by (apply IH; lia).
      assert (HT : FROM POST (u_j_inv B MT MS la_nul LF_MO_SET LF_MO_OP i j))
        by (eapply u_tail; eassumption).
      eapply u_head; try eassumption.
      eapply u_mid; try eassumption.
      eapply u_bret; eassumption. }
  intros j. apply (G (Z.to_nat (32 - j))). lia.
Qed.

End a.
