(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Plain.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec AllocIface.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure AllocCredit.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2MallocLayout O2Pins O2Alloc O2Sure O2Credit O2LeptBl_iface O2LeptBl2_iface O2LeptPbl_iface O2LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2MallocLayout V2Pins V2Alloc V2Sure V2Credit V2LeptBl_iface V2LeptBl2_iface V2LeptPbl_iface V2LeptPinsI.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Top Require Import BaseBilateralUbsanPre.

Theorem strong_universal_error_free_bilateral_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@bilateral_ubsan_pre _ _ (@acr_sure _ _ s16_credit) s16_pins (s16_fuzz_call s16_credit)
                              _ _ (@acr_sure _ _ u16_credit) u16_pins (u16_fuzz_call u16_credit)).
Qed.
