(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntryRaw), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* The hand-built allocation phase of LLVMFuzzerTestOneInput on the ASan build
   (fuzz_grant.c:363-387; slots 0x812ac .. 0x813b8): GI_raw reaches GI_sched0. The phase is
   the chain of its segments (GrantEntryRawDefs.v names the cuts):
     GI_raw -hd-> GR_hd -(one case per bytes of input left: rd0 | rd1 | rd2)-> GR_mal
       -malloc-> GR_bs1 -build_sweep-> GR_fit -alloc_fits-> GR_bs2
       -build_sweep (NULL sweep)-> GR_bs3 -build_sweep (NULL allocation)-> GR_free -free-> GI_sched0.
   reac_grant_build_sweep's contract is a Theorem Labs lane's `treac_grant_build_sweep_spec`; the
   segments use its statement `traw_bsw_spec`, and `traw_bsw_of` (GrantEntryRawDefs.v)
   passes from one to the other. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal GrantSyms GrantList GrantPa GrantPaLib GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantEntryDefs GrantEntryRawDefs GrantBuildSweep
GrantEntryRawHead GrantEntryRawRd0 GrantEntryRawRd1 GrantEntryRawRd2 GrantEntryRawMalloc GrantEntryRawBs1 GrantEntryRawFit GrantEntryRawBs2 GrantEntryRawBs3
GrantEntryRawFree.
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
Hypothesis BSW : treac_grant_build_sweep_spec B.

Theorem ge_raw : forall POST, ge_from B MT POST (GI_sched0 B MT) -> ge_from B MT POST (GI_raw B MT).
Proof.
intros POST H.
pose proof (traw_bsw_of B BSW) as BSWr.
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
