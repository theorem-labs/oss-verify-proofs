(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A, the PRIMED realloc walk record WITH the keep:
   YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh at segs := tfibsegs, ci := CfImg_A, (al, atp, acf, atpD) :=
   (8, 1, 1, 1), ARX := RGcfWalkA.ARXA B, K1 := RGcfK.K1A B, K2 := RGcfSegs2a.K2A B, K3 := RGcfSegs2a.K3A B, for every
   nmax, by YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh_of from the plain keep record of A/RGcfWalkA.v
   (wrap_realloc_walk_keep_cf_A) and the primed S3 with the keep of A/RGcfRetRhKeepA.v (rw_ret_keep_rh_A).
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfInstReallocKKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RGcfK RGcfSegs2a RGcfLaws RGcfWalkA RGcfRetRhKeepA.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_A.

Theorem wrap_realloc_walk_keep_cf_rh_A : forall (B : asyms) (TB : TfibSyms B) (nmax : Z),
  YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh tfibsegs B nmax 8 1 1 1 (RGcfWalkA.ARXA B)
    (RGcfK.K1A B) (RGcfSegs2a.K2A B) (RGcfSegs2a.K3A B).
Proof.
intros B TB nmax.
apply (YGcfInstReallocKKeep.wrap_realloc_walk_keep_cf_rh_of tfibsegs B nmax 8 1 1 1).
- exact (RGcfWalkA.wrap_realloc_walk_keep_cf_A B TB nmax).
- exact (RGcfRetRhKeepA.rw_ret_keep_rh_A B TB (RGcfLaws.rt_laws_aowned B TB)).
Qed.
End a.

Print Assumptions wrap_realloc_walk_keep_cf_rh_A.
