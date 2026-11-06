(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17Kit.
Import O17Kit.O17MallocLayout. Import O17Kit.O17Alloc. Import O17Kit.O17Sure. Import O17Kit.O17Credit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17Tail.
Import O17Tail.O17Pins. Import O17Tail.O17LeptPinsI.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17Kit.
Import V17Kit.V17MallocLayout. Import V17Kit.V17Alloc. Import V17Kit.V17Sure. Import V17Kit.V17Credit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17Tail.
Import V17Tail.V17Pins. Import V17Tail.V17LeptPinsI.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Top Require Import BaseKernelUbsanPre.

Theorem strong_universal_error_free_kernel_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@kernel_ubsan_pre _ _ (acr_sure (AllocCredit:=s17_credit)) O17Tail.O17Pins.s17_pins (s17_fuzz_call s17_credit)
                          _ _ (acr_sure (AllocCredit:=u17_credit)) V17Tail.V17Pins.u17_pins (u17_fuzz_call u17_credit)).
Qed.
