(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only Require Import AsanMain.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section WithFree.
  Hypothesis FREE : afree_stmt aci_I AHEAP_I.
  Hypothesis FUZZ : fuzz_oneA_stmt (AI_of FREE) afake_rng.
  Theorem adrv_of_free : adrv_stmt ATsafeMain.A0.
  Proof. exact (adrv (AI_of FREE) (AI_of_E FREE) (AI_of_CI_OK FREE) (AI_of_DRV_CI FREE) FUZZ). Qed.
End WithFree.
End CANSEC1.

Theorem asan_implC_of_free :
  forall FREE : (forall rc : runConstT, afree_stmt aci_I AHEAP_I),
  (forall rc : runConstT, fuzz_oneA_stmt (AI_of (FREE rc)) afake_rng) -> asan_implC_stmt ASTAGE.
Proof.
  intros FREE FUZZ. apply asan_implC_of_adrv. intros rc. exact (@adrv_of_free rc (FREE rc) (FUZZ rc)).
Qed.
