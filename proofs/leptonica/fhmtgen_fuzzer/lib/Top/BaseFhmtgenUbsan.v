(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Plain.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import AllocIface.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10Kit.
Import O10Kit.O10MallocLayout. Import O10Kit.O10Alloc. Import O10Kit.O10Sure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.O10 Require Import O10Tail.
Import O10Tail.O10Pins. Import O10Tail.O10LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Kit.
Import V10Kit.V10MallocLayout. Import V10Kit.V10Alloc. Import V10Kit.V10Sure.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.V10 Require Import V10Tail.
Import V10Tail.V10Pins. Import V10Tail.V10LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Top Require Import BaseFhmtgenUbsanPre.

Theorem strong_universal_error_free_fhmtgen_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@fhmtgen_ubsan_pre _ _ s16_sure O10Tail.O10Pins.s16_pins (s16_fuzz_call s16_sure)
                          _ _ u16_sure V10Tail.V10Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
