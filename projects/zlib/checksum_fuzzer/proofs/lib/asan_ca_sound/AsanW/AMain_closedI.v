(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import AsanMain.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require Import AImg AMalloc_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Theorem adrv_closedI : adrv_stmt ATsafeMain.A0.
Proof.
  exact (adrv (AI_of AHI_free) (AI_of_E AHI_free) (AI_of_CI_OK AHI_free) (AI_of_DRV_CI AHI_free)).
Qed.
End CANSEC1.

Theorem asan_impl_closed : asan_impl_stmt ASTAGE.
Proof.
  exact (asan_impl ATsafeMain.NMAX ATsafeMain.A0
           (fun rc : runConstT => @adrv_closedI rc)
           (fun rc : runConstT => @model_ok rc)
           ATsafeMain.A0_init).
Qed.
