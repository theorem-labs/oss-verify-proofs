(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Plain.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import AllocIface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Kit.
Import O15Kit.O15MallocLayout. Import O15Kit.O15Alloc. Import O15Kit.O15Sure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15Tail.
Import O15Tail.O15Pins. Import O15Tail.O15LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Kit.
Import V15Kit.V15MallocLayout. Import V15Kit.V15Alloc. Import V15Kit.V15Sure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15Tail.
Import V15Tail.V15Pins. Import V15Tail.V15LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top Require Import BaseGrayquantUbsanPre.

Theorem strong_universal_error_free_grayquant_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@grayquant_ubsan_pre _ _ s16_sure O15Tail.O15Pins.s16_pins (s16_fuzz_call s16_sure)
                          _ _ u16_sure V15Tail.V15Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
