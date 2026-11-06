(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.jpegiostub_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require Import O16Kit.
Import O16Kit.O16MallocLayout. Import O16Kit.O16Alloc. Import O16Kit.O16Sure.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.O16 Require Import O16Tail.
Import O16Tail.O16Pins. Import O16Tail.O16LeptPinsI.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.V16 Require Import V16Kit.
Import V16Kit.V16MallocLayout. Import V16Kit.V16Alloc. Import V16Kit.V16Sure.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.V16 Require Import V16Tail.
Import V16Tail.V16Pins. Import V16Tail.V16LeptPinsI.
From OSSVerify.Proofs.leptonica.jpegiostub_fuzzer.lib.Top Require Import BaseJpegiostubUbsanPre.

Theorem strong_universal_error_free_jpegiostub_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@jpegiostub_ubsan_pre _ _ s16_sure O16Tail.O16Pins.s16_pins (s16_fuzz_call s16_sure)
                          _ _ u16_sure V16Tail.V16Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
