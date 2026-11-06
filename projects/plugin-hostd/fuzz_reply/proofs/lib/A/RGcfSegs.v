(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset.asan image A, row A5: the realloc records' fields other than
   the prefixes (YGcfReallocCompose.wrap_realloc_walk_cf rw_mid_a, rw_memcpy, rw_mid_b, rw_ret, rw_nret;
   wrap_realloc_null_walk_cf rwn_post) at segs := tfibsegs, ci := CfImg_A, (al, atp, acf, atpD) := (8, 1, 1, 1),
   ARX := RGcfLaws.ARXqA B, K1 := RGcfK.K1A B, K2 := K2A B, K3 := K3A B, Kn := RGcfK.KnA, for every nmax:
   A/RGcfSegs2a.v (K2A, K3A, rw_mid_a_A), A/RGcfMemcpy.v (rw_memcpy_A), A/RGcfSegs2b.v (rw_mid_b_A), A/RGcfSegs3.v
   (rw_ret_A), A/RGcfSegs4.v (rw_nret_A), A/RGcfSegs6.v (rwn_post_A); their premises are TfibSyms B and the allocator
   laws LAWSa / LAWSm, which A/RGcfLaws.v proves (rt_laws_aowned / rt_laws_aoxm). walk_of_pre / null_walk_of_pre apply
   the records' constructors to these theorems (with RGcfLaws's laws) after any prefix field, so each theorem's type is
   its field's at the instance. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AF0m CfImgA.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require YGcfMallocCompose YGcfReallocCompose.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require RGcfK RGcfLaws.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Export RGcfSegs2a RGcfMemcpy RGcfSegs2b RGcfSegs3 RGcfSegs4 RGcfSegs6.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_A.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable nmax : Z.

Definition walk_of_pre :=
fun pre => @YGcfReallocCompose.Build_wrap_realloc_walk_cf _ _ _ _ tfibsegs B nmax 8 1 1 1
  (fun Hp inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md) (RGcfK.K1A B) (K2A B) (K3A B)
  pre
  (rw_mid_a_A B TB (RGcfLaws.rt_laws_aowned B TB) (RGcfLaws.rt_laws_aoxm B TB) nmax)
  rw_memcpy_A
  (rw_mid_b_A B TB (RGcfLaws.rt_laws_aowned B TB) (RGcfLaws.rt_laws_aoxm B TB))
  (rw_ret_A B TB (RGcfLaws.rt_laws_aowned B TB) (RGcfLaws.rt_laws_aoxm B TB))
  (rw_nret_A B TB (RGcfLaws.rt_laws_aowned B TB) (RGcfLaws.rt_laws_aoxm B TB) nmax).

Definition null_walk_of_pre :=
fun pre => @YGcfReallocCompose.Build_wrap_realloc_null_walk_cf _ _ _ _ tfibsegs B nmax 8 1 1
  (fun Hp inst ly S W mem md => RGcfLaws.ARXqA B Hp inst ly S W mem md) RGcfK.KnA
  pre
  (rwn_post_A B TB (RGcfLaws.rt_laws_aowned B TB) (RGcfLaws.rt_laws_aoxm B TB) nmax).
End a.

Print Assumptions rw_mid_a_A.
Print Assumptions rw_memcpy_A.
Print Assumptions rw_mid_b_A.
Print Assumptions rw_ret_A.
Print Assumptions rw_nret_A.
Print Assumptions rwn_post_A.
Print Assumptions walk_of_pre.
Print Assumptions null_walk_of_pre.
