(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.paintcmap_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21Kit.
Import O21Kit.O21MallocLayout. Import O21Kit.O21Alloc. Import O21Kit.O21Sure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.O21 Require Import O21Tail.
Import O21Tail.O21Pins. Import O21Tail.O21LeptPinsI.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21Kit.
Import V21Kit.V21MallocLayout. Import V21Kit.V21Alloc. Import V21Kit.V21Sure.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.V21 Require Import V21Tail.
Import V21Tail.V21Pins. Import V21Tail.V21LeptPinsI.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Top Require Import BasePaintcmapUbsanPre.

Theorem strong_universal_error_free_paintcmap_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@paintcmap_ubsan_pre _ _ s21_sure O21Tail.O21Pins.s21_pins (s21_fuzz_call s21_sure)
                          _ _ u21_sure V21Tail.V21Pins.u21_pins (u21_fuzz_call u21_sure)).
Qed.
