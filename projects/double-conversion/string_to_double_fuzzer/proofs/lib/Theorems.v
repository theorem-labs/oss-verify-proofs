(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.
Require OSSVerify.double_conversion.string_to_double_fuzzer.images.Asan.
Require OSSVerify.double_conversion.string_to_double_fuzzer.images.Ubsan.
Require OSSVerify.double_conversion.string_to_double_fuzzer.images.AsanUbsan.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require ImgSame LxLib BaseUbsan AsanFinal BothFinal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Theorem strong_universal_error_free_string_to_double_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets_abort
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.loaded_segments OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.init_pc OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.double_conversion.string_to_double_fuzzer.images.Asan.M.loaded_segments OSSVerify.double_conversion.string_to_double_fuzzer.images.Asan.M.init_pc OSSVerify.double_conversion.string_to_double_fuzzer.images.Asan.M.phdrs).
Proof.
  rewrite <- ImgSame.image_P_same, <- ImgSame.image_A_same.
  exact AsanFinal.asan_final_abort.
Qed.

Theorem strong_universal_error_free_string_to_double_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets_abort
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.loaded_segments OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.init_pc OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.double_conversion.string_to_double_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.double_conversion.string_to_double_fuzzer.images.Ubsan.M.init_pc OSSVerify.double_conversion.string_to_double_fuzzer.images.Ubsan.M.phdrs).
Proof.
  rewrite <- ImgSame.image_P_same, <- ImgSame.image_U_same.
  exact (BaseUbsan.ubsan_base_abort LxLib.lib_P LxLib.lib_U).
Qed.

Theorem strong_universal_error_free_string_to_double_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_budgets_abort
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.loaded_segments OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.init_pc OSSVerify.double_conversion.string_to_double_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.double_conversion.string_to_double_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.double_conversion.string_to_double_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.double_conversion.string_to_double_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  rewrite <- ImgSame.image_P_same, <- ImgSame.image_B_same.
  exact BothFinal.both_final_abort.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
