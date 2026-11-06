(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfWalkA.v, with its module paths and module names changed; 23 of its 39 lines of code are new or changed and 5 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10-31: the realloc KEEP records at image A (wrap_realloc_walk_keep_cf_A /
   wrap_realloc_null_walk_keep_cf_A, from the keep forms of the segment theorems), and the plain records, with the
   same statements as before, by YGcfReallocComposeKeep.wrap_realloc_walk_cf_of_keep /
   wrap_realloc_null_walk_cf_of_keep. *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A, row A5 of the internal file FREE-PIECES-102.md: A4's realloc records
   YGcfReallocCompose.wrap_realloc_walk_cf and wrap_realloc_null_walk_cf, and their keep forms
   YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf and wrap_realloc_null_walk_keep_cf, at image A
   (segs := tfibsegs, ci := CfImg_A, (al, atp, acf, atpD) := (8, 1, 1, 1), ARX := RGcfLaws.ARXqA B, K1 := RGcfK.K1A B,
   K2 := RGcfSegs2a.K2A B, K3 := RGcfSegs2a.K3A B, Kn := RGcfK.KnA, for every nmax), from rw_pre_A (A/RGcfS1.v),
   rwn_pre_A (A/RGcfS5.v) and the other fields (A/RGcfSegs.v walk_of_pre / null_walk_of_pre), with the allocator laws
   of A/RGcfLaws.v. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf YG0scf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AF0m CfImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfReallocCompose YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RGcfK RGcfS1 RGcfS5 RGcfSegs2a RGcfSegs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require RGcfLaws.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_A.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable nmax : Z.

Definition ARXA : YGcfMallocCompose.ARXh_t tfibsegs :=
fun Hp inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md.

Theorem wrap_realloc_walk_keep_cf_A :
YGcfReallocComposeKeep.wrap_realloc_walk_keep_cf tfibsegs B nmax 8 1 1 1 ARXA (RGcfK.K1A B) (RGcfSegs2a.K2A B)
  (RGcfSegs2a.K3A B).
Proof. exact (RGcfSegs.walk_of_pre B TB nmax (RGcfS1.rw_pre_A B TB nmax)). Qed.

Theorem wrap_realloc_null_walk_keep_cf_A :
YGcfReallocComposeKeep.wrap_realloc_null_walk_keep_cf tfibsegs B nmax 8 1 1 ARXA RGcfK.KnA.
Proof. exact (RGcfSegs.null_walk_of_pre B TB nmax (RGcfS5.rwn_pre_A B TB nmax)). Qed.

Theorem wrap_realloc_walk_cf_A :
YGcfReallocCompose.wrap_realloc_walk_cf tfibsegs B nmax 8 1 1 1 ARXA (RGcfK.K1A B) (RGcfSegs2a.K2A B) (RGcfSegs2a.K3A B).
Proof. apply YGcfReallocComposeKeep.wrap_realloc_walk_cf_of_keep. exact wrap_realloc_walk_keep_cf_A. Qed.

Theorem wrap_realloc_null_walk_cf_A :
YGcfReallocCompose.wrap_realloc_null_walk_cf tfibsegs B nmax 8 1 1 ARXA RGcfK.KnA.
Proof. apply YGcfReallocComposeKeep.wrap_realloc_null_walk_cf_of_keep. exact wrap_realloc_null_walk_keep_cf_A. Qed.
End a.

Print Assumptions wrap_realloc_walk_keep_cf_A.
Print Assumptions wrap_realloc_null_walk_keep_cf_A.
Print Assumptions wrap_realloc_walk_cf_A.
Print Assumptions wrap_realloc_null_walk_cf_A.
