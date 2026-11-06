(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/RGcfWalkA.v at commit 6ea216c338f as lib/B/RGcfWalkB.v, with its module paths changed (lib.A to lib.B, except the image-free ADIfaceImgA and the one params file CfParamsReply; the image twins A<r> to Y<r>, CfImgA / CfImg_A to CfImgB / CfImg_B, WrapAKit / WrapFreeA<x> to WrapBKit / WrapFreeB<x>, AFf0cfR to YFf0cfR, RGcfWalkA to RGcfWalkB with its three exported names wrap_realloc_walk_cf_A, wrap_realloc_null_walk_cf_A, wrap_realloc_walk_cf_rh_A to _B), and no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* Theorem Labs, 2026-10-31 (a Theorem Labs lane, for a Theorem Labs lane's reply-A realloc row): reply image A's realloc walk records,
   relocated from fuzz_preset's lib/A/RGcfWalkA.v (commit dc970db26dad; only the module
   prefixes change, the texts carry no image constant) and extended with the PRIMED record reply's realloc top takes:
     wrap_realloc_walk_cf_A        : YGcfReallocCompose.wrap_realloc_walk_cf (unprimed), from RGcfS1.rw_pre_A and the
                                     other fields (RGcfSegs.walk_of_pre);
     wrap_realloc_null_walk_cf_A   : YGcfReallocCompose.wrap_realloc_null_walk_cf, from RGcfS5.rwn_pre_A and
                                     RGcfSegs.null_walk_of_pre (RGcfSegs6.rwn_post_A);
     wrap_realloc_walk_cf_rh_A     : YGcfReallocComposeRh.wrap_realloc_walk_cf_rh (PRIMED), the unprimed record with
                                     its return segment replaced by RGcfSegs3Rh.rw_ret_rh_A (Deallocate's primed raw
                                     post), by YGcfReallocComposeRh.wrap_realloc_walk_cf_rh_of;
   all at segs := tfibsegs, ci := CfImg_A, (al, atp, acf, atpD) := (8, 1, 1, 1), ARX := RGcfLaws.ARXqA B,
   K1 := RGcfK.K1A B, K2 := RGcfSegs2a.K2A B, K3 := RGcfSegs2a.K3A B, Kn := RGcfK.KnA, for every nmax; the allocator
   laws are A/RGcfLaws.v's rt_laws_aowned / rt_laws_aoxm.
   rule 24: proves no function (kind: record assembly over proved segment walks). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YF0m CfImgB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YGcfMallocCompose YGcfReallocCompose YGcfReallocComposeRh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGcfK RGcfS1 RGcfS5 RGcfSegs2a RGcfSegs RGcfSegs3Rh.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require RGcfLaws.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_B.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable nmax : Z.

Definition ARXA : YGcfMallocCompose.ARXh_t tfibsegs :=
fun Hp inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md.

Theorem wrap_realloc_walk_cf_B :
YGcfReallocCompose.wrap_realloc_walk_cf tfibsegs B nmax 8 1 1 1 ARXA (RGcfK.K1A B) (RGcfSegs2a.K2A B) (RGcfSegs2a.K3A B).
Proof. exact (RGcfSegs.walk_of_pre B TB nmax (RGcfS1.rw_pre_A B TB nmax)). Qed.

Theorem wrap_realloc_null_walk_cf_B :
YGcfReallocCompose.wrap_realloc_null_walk_cf tfibsegs B nmax 8 1 1 ARXA RGcfK.KnA.
Proof. exact (RGcfSegs.null_walk_of_pre B TB nmax (RGcfS5.rwn_pre_A B TB nmax)). Qed.

(* the primed record: the released record and the primed return segment *)
Theorem wrap_realloc_walk_cf_rh_B :
YGcfReallocComposeRh.wrap_realloc_walk_cf_rh tfibsegs B nmax 8 1 1 1 ARXA (RGcfK.K1A B) (RGcfSegs2a.K2A B)
  (RGcfSegs2a.K3A B).
Proof.
exact (YGcfReallocComposeRh.wrap_realloc_walk_cf_rh_of tfibsegs B nmax 8 1 1 1 ARXA (RGcfK.K1A B) (RGcfSegs2a.K2A B)
  (RGcfSegs2a.K3A B) wrap_realloc_walk_cf_B
  (RGcfSegs3Rh.rw_ret_rh_A B TB (RGcfLaws.rt_laws_aowned B TB) (RGcfLaws.rt_laws_aoxm B TB))).
Qed.
End a.

Print Assumptions wrap_realloc_walk_cf_B.
Print Assumptions wrap_realloc_null_walk_cf_B.
Print Assumptions wrap_realloc_walk_cf_rh_B.
