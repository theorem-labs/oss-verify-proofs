(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound Require Import CkTop.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require Import MainEntryBoth.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.FO Require FOCore.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import HaltsB.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import ProgExits.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound Require Import BothMain.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import BImg ADriver_iface AMain_closedI.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Theorem base_both_closed :
  strong_universal_error_free_T_scfg_budgets FOCore.alloc_forced_cfg SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (base_both ASTAGE both_impl_closed). Qed.

Theorem base_both_plain_closed :
  strong_universal_error_free_T_scfg FOCore.alloc_forced_cfg
    (mkImage psegs p_init_pc p_phdrs)
    (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (base_both_plain ASTAGE both_impl_closed). Qed.

Theorem halts_both_closed :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source AnyExit.codes (mkImage bsegs b_init_pc b_phdrs).
Proof. exact (halts_both ASTAGE both_impl_closed). Qed.

Theorem halts_both_closedB :
  halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source [Z_to_bv 64 0; Z_to_bv 64 2] (mkImage bsegs b_init_pc b_phdrs).
Proof.
  apply (halts_B_of_srealizes bsegs b_init_pc b_phdrs (TA (2^31)%Z)). intros en inp Hv Hi. cbv zeta. split.
  - exact (both_side_srz_lim (TA (2^31)%Z) source_alloc_limit (Z.le_refl _)
             (both_side_main ASTAGE both_impl_closed (2^31)%Z (Z.le_refl _)) en inp Hv Hi).
  - unfold TA. apply prog_ends_in_02.
Qed.

