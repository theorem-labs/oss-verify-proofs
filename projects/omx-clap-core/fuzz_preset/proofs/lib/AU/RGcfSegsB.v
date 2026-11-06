(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: relocated from proofs/omx-clap-core/fuzz_preset/lib/A/RGcfSegs.v (hub 48d2e915d556, blob 49cac2da4d48), stated at fuzz_preset's asan image (ELF sha256 bff8519bbe3e), to its asan-ubsan image (ELF sha256 c90d4fa54d43): module paths to the image-B twins, every image numeral by symbol + offset, image bounds by the image-B start-up facts; comments removed (the source file keeps them). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YG00 YG0f YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import CfImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfMallocCompose YGcfReallocCompose YGcfReallocComposeKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require RGcfKB RGcfLawsB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Export RGcfSegs2aB RGcfMemcpyB RGcfMemcpyKeepB RGcfSegs2bB RGcfSegs3B RGcfSegs4B RGcfSegs6B.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Local Existing Instance CfImg_B.
Variable B : asyms.
Hypothesis TB : TfibSyms B.
Variable nmax : Z.

Definition walk_of_pre :=
fun pre => @YGcfReallocComposeKeep.Build_wrap_realloc_walk_keep_cf _ _ _ _ tfibsegs B nmax 8 1 1 1
  (fun Hp inst ly S W mem md => RGcfLawsB.ARXqB B Hp inst ly S W mem md) (RGcfKB.K1B B) (K2B B) (K3B B)
  pre
  (rw_mid_a_B B TB (RGcfLawsB.rt_laws_aowned B TB) (RGcfLawsB.rt_laws_aoxm B TB) nmax)
  rw_memcpy_keep_B
  (rw_mid_b_B B TB (RGcfLawsB.rt_laws_aowned B TB) (RGcfLawsB.rt_laws_aoxm B TB))
  (rw_ret_B B TB (RGcfLawsB.rt_laws_aowned B TB) (RGcfLawsB.rt_laws_aoxm B TB))
  (rw_nret_B B TB (RGcfLawsB.rt_laws_aowned B TB) (RGcfLawsB.rt_laws_aoxm B TB) nmax).

Definition null_walk_of_pre :=
fun pre => @YGcfReallocComposeKeep.Build_wrap_realloc_null_walk_keep_cf _ _ _ _ tfibsegs B nmax 8 1 1
  (fun Hp inst ly S W mem md => RGcfLawsB.ARXqB B Hp inst ly S W mem md) RGcfKB.KnB
  pre
  (rwn_post_B B TB (RGcfLawsB.rt_laws_aowned B TB) (RGcfLawsB.rt_laws_aoxm B TB) nmax).
End a.

Print Assumptions rw_mid_a_B.
Print Assumptions rw_memcpy_B.
Print Assumptions rw_memcpy_keep_B.
Print Assumptions rw_mid_b_B.
Print Assumptions rw_ret_B.
Print Assumptions rw_nret_B.
Print Assumptions rwn_post_B.
Print Assumptions walk_of_pre.
Print Assumptions null_walk_of_pre.
