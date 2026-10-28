(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec AllocIface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23MallocLayout O23Pins O23Alloc O23Sure O23Credit O23LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23MallocLayout V23Pins V23Alloc V23Sure V23Credit V23LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Top Require Import BasePixOrientUbsanPre.

Theorem strong_universal_error_free_pix_orient_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@pix_orient_ubsan_pre _ _ (@acr_sure _ _ s16_credit) s16_pins (s16_fuzz_call s16_credit)
                               _ _ (@acr_sure _ _ u16_credit) u16_pins (u16_fuzz_call u16_credit)).
Qed.
