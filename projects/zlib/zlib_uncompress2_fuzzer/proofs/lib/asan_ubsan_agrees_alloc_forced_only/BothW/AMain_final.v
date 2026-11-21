(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only Require Import ZTopC BothMain.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition harness_closed_stmt : Prop := forall rc : runConstT, fuzz_oneA_stmt (AI_of (@AHI_free rc)) afake_rng.

Theorem both_implC_final : harness_closed_stmt -> both_implC_stmt ASTAGE.
Proof. intros HARNESS. exact (both_implC_of_free (fun rc : runConstT => @AHI_free rc) HARNESS). Qed.
