(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRaw), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntryRaw.v. *)
(* Ported from lib/A/Prog/GrantEntryRaw.v of a working branch 7c8c67da870 (blob 17ba816574a). *)
(* The hand-built allocation phase of LLVMFuzzerTestOneInput on image B
   (fuzz_grant.c:363-387; slots 0x8181c .. 0x81944): GI_raw reaches GI_sched0. The phase is
   the chain of its segments (LLVMFEntryRawDefs.v names the cuts):
     GI_raw -hd-> GR_hd -(one case per bytes of input left: rd0 | rd1 | rd2)-> GR_mal
       -malloc-> GR_bs1 -build_sweep-> GR_fit -alloc_fits-> GR_bs2
       -build_sweep (NULL sweep)-> GR_bs3 -build_sweep (NULL allocation)-> GR_free -free-> GI_sched0.
   reac_grant_build_sweep's contract is tb_reac_grant_build_sweep_spec and
   reac_grant_alloc_fits's is tb_reac_grant_alloc_fits_spec (GrantBContracts.v); both are
   hypotheses of walk_LLVMFuzzerTestOneInput, and this phase takes them as arguments. Image A
   called reac_grant_alloc_fits through its closed walk instead.

   Every branch out of the range to an error slot is refuted: the abort 0x81d98 after
   malloc (0x818b8), after the check of the first sweep's answer (0x818fc, 0x81904) and
   after the two refused sweeps (0x81924, 0x81938); the UBSan trap 0x81f48 from the two
   cursor checks (0x81830, 0x8187c); and the input checks' slow paths 0x81f90 and 0x81fcc,
   which call __asan_report_load1, from the shadow entries of the input block. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib GrantBContracts LLVMFEntryDefs LLVMFEntryRawDefs.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
LLVMFEntryRawHead LLVMFEntryRawRd0 LLVMFEntryRawRd1 LLVMFEntryRawRd2 LLVMFEntryRawMalloc
LLVMFEntryRawBs1 LLVMFEntryRawFit LLVMFEntryRawBs2 LLVMFEntryRawBs3 LLVMFEntryRawFree.
Import ListNotations.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section b. Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).
Section c.
Variable B : asyms.
Variable MT : ameter_ops.

Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis AMALLOC4 : amalloc04_rule SEGS B MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis FITS : tb_reac_grant_alloc_fits_spec B.
Hypothesis BSW : tb_reac_grant_build_sweep_spec B.

Theorem ge_raw : forall POST, ge_from B MT POST (GI_sched0 B MT) -> ge_from B MT POST (GI_raw B MT).
Proof.
intros POST H.
assert (HF : ge_from B MT POST (GR_freeI B MT)) by (eapply seg_raw_free; eassumption).
assert (H3 : ge_from B MT POST (GR_bs3I B MT)) by (eapply seg_raw_bs3; eassumption).
assert (H2 : ge_from B MT POST (GR_bs2I B MT)) by (eapply seg_raw_bs2; eassumption).
assert (HT : ge_from B MT POST (GR_fitI B MT)) by (eapply seg_raw_fit; eassumption).
assert (H1 : ge_from B MT POST (GR_bs1I B MT)) by (eapply seg_raw_bs1; eassumption).
assert (HM : ge_from B MT POST (GR_malI B MT)) by (eapply seg_raw_mal; eassumption).
assert (HD : ge_from B MT POST (GR_hdI B MT)).
{ eapply seg_raw_split; try eassumption;
    first [ eapply seg_raw_rd0 | eapply seg_raw_rd1 | eapply seg_raw_rd2 ]; eassumption. }
eapply seg_raw_hd; eassumption.
Qed.

End c.
End b.
End a.
