(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.

Require OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.
Require OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.
Require OssFuzzTheorems.zstd.zstd_frame_info.images.Ubsan.
Require OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.
Require OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.AsanW.ABase_final.
Require OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.BothW.ABase_final.
Require OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.HaltsAsanBClosed.
Require OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.HaltsBothBClosed.

Module HaltsCfgForcedOnly <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.forced_only_cfg.
End HaltsCfgForcedOnly.

Module ZstdZstdFrameInfoHaltsAsanExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End ZstdZstdFrameInfoHaltsAsanExits.

Module ZstdZstdFrameInfoHaltsBothExits <: LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.ALLOWED_EXITS.
  Import stdpp.bitvector.bitvector.
  Import ListNotations.
  Definition codes : list (stdpp.bitvector.definitions.bv 64) := [Z_to_bv 64 0; Z_to_bv 64 2].
End ZstdZstdFrameInfoHaltsBothExits.
Require OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.UbsanMain.

Theorem strong_universal_error_free_zstd_frame_info_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.AsanW.ABase_final.base_asan_closed.
Qed.

Theorem strong_universal_error_free_zstd_frame_info_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.Ubsan.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.Ubsan.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.Ubsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.UbsanMain.base_ubsan.
Qed.

Theorem strong_universal_error_free_zstd_frame_info_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.BothW.ABase_final.base_both_closed.
Qed.

Theorem halts_allowed_zstd_zstd_frame_info_halts_asan :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    ZstdZstdFrameInfoHaltsAsanExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.Asan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.HaltsAsanBClosed.halts_asanB.
Qed.

Theorem halts_allowed_zstd_zstd_frame_info_halts_both :
  LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.halts_allowed_T_scfg_budgets
    HaltsCfgForcedOnly.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    ZstdZstdFrameInfoHaltsBothExits.codes
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.M.init_pc OssFuzzTheorems.zstd.zstd_frame_info.images.AsanUbsan.M.phdrs).
Proof.
  exact OssFuzzTheorems.Proofs.zstd.zstd_frame_info.lib.HaltsBothBClosed.halts_bothB.
Qed.
