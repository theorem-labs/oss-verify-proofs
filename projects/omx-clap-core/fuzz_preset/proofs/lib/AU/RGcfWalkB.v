(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfWalkA.v (hub 48d2e915d556, blob 124c21cd5620), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfReallocCompose YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RGcfKB RGcfS1B RGcfS5B RGcfSegs2aB RGcfSegsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RGcfLawsB.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_B.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable nmax : Z.

Definition ARXB : YGcfMallocCompose.ARXh_t tfibsegs :=
fun Hp inst ly S W mem md => RGcfLawsB.ARXqB B Hp inst ly S W mem md.

Theorem wrap_realloc_walk_keep_cf_B :
YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf tfibsegs B nmax 8 1 1 1 ARXB (RGcfKB.K1B B) (RGcfSegs2aB.K2B B)
  (RGcfSegs2aB.K3B B).
Proof. exact (RGcfSegsB.walk_of_pre B TB nmax (RGcfS1B.rw_pre_B B TB nmax)). Qed.

Theorem wrap_realloc_null_walk_keep_cf_B :
YGcfReallocComposeKeep.wrap_realloc_null_walk_keep_cf tfibsegs B nmax 8 1 1 ARXB RGcfKB.KnB.
Proof. exact (RGcfSegsB.null_walk_of_pre B TB nmax (RGcfS5B.rwn_pre_B B TB nmax)). Qed.

Theorem wrap_realloc_walk_cf_B :
YGcfReallocCompose.wrap_realloc_walk_cf tfibsegs B nmax 8 1 1 1 ARXB (RGcfKB.K1B B) (RGcfSegs2aB.K2B B) (RGcfSegs2aB.K3B B).
Proof. apply YGcfReallocComposeKeep.wrap_realloc_walk_cf_of_keep. exact wrap_realloc_walk_keep_cf_B. Qed.

Theorem wrap_realloc_null_walk_cf_B :
YGcfReallocCompose.wrap_realloc_null_walk_cf tfibsegs B nmax 8 1 1 ARXB RGcfKB.KnB.
Proof. apply YGcfReallocComposeKeep.wrap_realloc_null_walk_cf_of_keep. exact wrap_realloc_null_walk_keep_cf_B. Qed.
End a.

Print Assumptions wrap_realloc_walk_keep_cf_B.
Print Assumptions wrap_realloc_null_walk_keep_cf_B.
Print Assumptions wrap_realloc_walk_cf_B.
Print Assumptions wrap_realloc_null_walk_cf_B.
