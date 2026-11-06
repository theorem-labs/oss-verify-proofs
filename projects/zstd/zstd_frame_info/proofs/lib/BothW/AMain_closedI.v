(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import BothMain.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.

Section CANSEC1. Context {rc : runConstT}.
Section WithFree.
  Hypothesis FREE : afree_stmt aci_I AHEAP_I.
  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_oneA_stmt (AI_of FREE) AFake_iface.afake_rng.

  #[using="FREE FUZZ"] Theorem adrv_of_free : adrv_stmt ATsafeMain.A0.
  Proof.
    exact (adrv (AI_of FREE) (AI_of_E FREE) (AI_of_CI_OK FREE) (AI_of_DRV_CI FREE) (AI_of_CLI_CI FREE) FUZZ).
  Qed.
End WithFree.
End CANSEC1.

(* [comment removed for export] *)
Theorem both_impl_of_free :
  forall FREE : (forall rc : runConstT, afree_stmt aci_I AHEAP_I),
  (forall rc : runConstT, fuzz_oneA_stmt (AI_of (FREE rc)) AFake_iface.afake_rng) -> both_impl_stmt ASTAGE.
Proof.
  intros FREE FUZZ.
  exact (both_impl ATsafeMain.NMAX ATsafeMain.A0
           (fun rc : runConstT => @adrv_of_free rc (FREE rc) (FUZZ rc))
           (fun rc : runConstT => @model_ok rc)
           ATsafeMain.A0_init).
Qed.
