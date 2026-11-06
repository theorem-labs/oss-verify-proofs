(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: image-B walk segment; lines 47-55 follow the shape of cgif_file_fuzzer lib/A/AC8a.v:28 (licscan run). *)
(* The SWEEP phase of fuzz_grant's entry function on IMAGE B: its eight segments
   composed. `ge_sweep` is what the phase before it (the admission tests) applies, and
   it hands on to the phase that walks the hand-built allocation.

   Adapted from lib/A/Prog/GrantEntrySweep.v (a working branch afd75724b5b, blob 2859b8cb4,
   89 lines), which carries no licence header of its own.
   Image B's read-only tables come from one premise,
   `GrantBContracts.IMG_LLVMF_SWEEP`, which `hyps_LLVMFuzzerTestOneInput` holds, where
   image A's walk took fifteen separate Hypotheses and its image instance discharged them;
   `want_of` is a real call on image B, so the phase takes `tb_want_of_spec` and not
   image A's `treac_headamp_default_spec`; and image B's group-B loop builds each poll
   row with `reac_ctrl_identity_poll_block` instead of reading image A's GROUPB table,
   so object 19's bytes are the callee's premise, not this phase's. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantRo GrantFrame GrantBContracts
LLVMFEntryDefs LLVMFEntrySweepDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntrySweepS1c LLVMFEntrySweepS1 LLVMFEntrySweepS1b LLVMFEntrySweepS1s
LLVMFEntrySweepS2 LLVMFEntrySweepS3c LLVMFEntrySweepS3 LLVMFEntrySweepS3d
LLVMFEntrySweepS3a LLVMFEntrySweepS3b LLVMFEntrySweepS4.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel GrantModel GrantSweepModel BuildSweepModel SweepRowCheck GrantSlotPlan.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require SlotNeeds_c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
#[local] Notation GF := (fun GI => ge_from B MT (ge_post B MT) GI).

(* What the segments take beyond the runtime: image B's four read-only tables, which
   `hyps_LLVMFuzzerTestOneInput` gives, and the four callees of the phase. *)
Theorem ge_sweep :
  GSW_RT B MT -> GSW_IMG B ->
  tb_reac_grant_build_sweep_spec B ->
  tb_want_of_spec B ->
  tb_check_groupa_spec B ->
  tb_reac_ctrl_identity_poll_block_spec B ->
  GF (GI_raw B MT) -> GF (GI_sweep B MT).
Proof.
intros HRT HIMG TBSW TWANT TCG TIPB HN.
assert (HF : GF (GIS_free1 B MT)) by (apply gsw_seg_free1; assumption).
assert (HB : GF (GIS_gbhd B MT)) by (apply (gsw_seg_gb B MT TIPB); assumption).
assert (HG1 : GF (GIS_ga1 B MT)) by (apply (gsw_seg_ga1 B MT TWANT TCG); assumption).
assert (HG0 : GF (GIS_ga0 B MT)) by (apply (gsw_seg_ga0 B MT TWANT TCG); assumption).
assert (HX : GF (GIS_rowex B MT)) by (apply gsw_seg_heads; assumption).
assert (HH : GF (GIS_rowhd B MT)) by (apply gsw_seg_rows; assumption).
assert (HM : GF (GIS_mal B MT)) by (apply (gsw_seg_mal B MT TBSW); assumption).
apply gsw_seg_sweep; assumption.
Qed.

End c.
End b.
End a.
