(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfWalkKeepRhA.v (hub 3a5414cdb2eb, blob 42e59cb60690), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RGcfKB RGcfSegs2aB RGcfLawsB RGcfWalkB RGcfRetRhKeepB.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_B.

Theorem wrap_realloc_walk_keep_cf_rh_B : forall (B : asyms) (TB : TfibSyms B) (nmax : Z),
  YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh tfibsegs B nmax 8 1 1 1 (RGcfWalkB.ARXB B)
    (RGcfKB.K1B B) (RGcfSegs2aB.K2B B) (RGcfSegs2aB.K3B B).
Proof.
intros B TB nmax.
apply (YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh_of tfibsegs B nmax 8 1 1 1).
- exact (RGcfWalkB.wrap_realloc_walk_keep_cf_B B TB nmax).
- exact (RGcfRetRhKeepB.rw_ret_keep_rh_B B TB (RGcfLawsB.rt_laws_aowned B TB)).
Qed.
End a.

Print Assumptions wrap_realloc_walk_keep_cf_rh_B.
