(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import AllocIface.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocAllocLayout AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Kit.
Import O14Kit.O14MallocLayout. Import O14Kit.O14Alloc. Import O14Kit.O14Sure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14Tail.
Import O14Tail.O14Pins. Import O14Tail.O14LeptPinsI.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14Kit.
Import V14Kit.V14MallocLayout. Import V14Kit.V14Alloc. Import V14Kit.V14Sure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14Tail.
Import V14Tail.V14Pins. Import V14Tail.V14LeptPinsI.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Top Require Import BaseGraymorphUbsanPre.

Theorem strong_universal_error_free_graymorph_fuzzer_ubsan :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false) ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  exact (@graymorph_ubsan_pre _ _ s16_sure O14Tail.O14Pins.s16_pins (s16_fuzz_call s16_sure)
                          _ _ u16_sure V14Tail.V14Pins.u16_pins (u16_fuzz_call u16_sure)).
Qed.
