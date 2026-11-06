(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8Kit.
Import O8Kit.O8MallocLayout. Import O8Kit.O8Alloc. Import O8Kit.O8Sure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.O8 Require Import O8Tail.
Import O8Tail.O8Pins. Import O8Tail.O8LeptPinsI.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8Kit.
Import V8Kit.V8MallocLayout. Import V8Kit.V8Alloc. Import V8Kit.V8Sure.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.V8 Require Import V8Tail.
Import V8Tail.V8Pins. Import V8Tail.V8LeptPinsI.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Top Require Import BaseColorfillUbsanPre.

Theorem strong_universal_error_free_colorfill_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@colorfill_ubsan_pre _ _ s8_sure O8Tail.O8Pins.s8_pins (s8_fuzz_call s8_sure)
                          _ _ u8_sure V8Tail.V8Pins.u8_pins (u8_fuzz_call u8_sure)).
Qed.
