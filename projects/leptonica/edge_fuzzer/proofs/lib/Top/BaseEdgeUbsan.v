(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9Kit.
Import O9Kit.O9MallocLayout. Import O9Kit.O9Alloc. Import O9Kit.O9Sure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.O9 Require Import O9Tail.
Import O9Tail.O9Pins. Import O9Tail.O9LeptPinsI.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9Kit.
Import V9Kit.V9MallocLayout. Import V9Kit.V9Alloc. Import V9Kit.V9Sure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9Tail.
Import V9Tail.V9Pins. Import V9Tail.V9LeptPinsI.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Top Require Import BaseEdgeUbsanPre.

Theorem strong_universal_error_free_edge_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@edge_ubsan_pre _ _ s16_sure O9Tail.O9Pins.s16_pins (s16_fuzz_call s16_sure)
                          _ _ u16_sure V9Tail.V9Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
