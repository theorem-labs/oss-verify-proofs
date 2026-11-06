(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.pix1_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Kit.
Import O22Kit.O22MallocLayout. Import O22Kit.O22Alloc. Import O22Kit.O22Sure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.O22 Require Import O22Tail.
Import O22Tail.O22Pins. Import O22Tail.O22LeptPinsI.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require Import V22Kit.
Import V22Kit.V22MallocLayout. Import V22Kit.V22Alloc. Import V22Kit.V22Sure.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.V22 Require Import V22Tail.
Import V22Tail.V22Pins. Import V22Tail.V22LeptPinsI.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Top Require Import BasePix1UbsanPre.

Theorem strong_universal_error_free_pix1_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@pix1_ubsan_pre _ _ s22_sure O22Tail.O22Pins.s22_pins (s22_fuzz_call s22_sure)
                          _ _ u22_sure V22Tail.V22Pins.u22_pins (u22_fuzz_call u22_sure)).
Qed.
