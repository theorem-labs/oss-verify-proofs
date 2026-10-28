(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require LinuxProcessSemantics.EquivalenceDefinition.HaltsAllowed.
Require OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.
Require OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Asan.
Require OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.
Require OssFuzzTheorems.leptonica.grayquant_fuzzer.images.AsanUbsan.

Require OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top.BaseGrayquantAsan.
Require OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top.BaseGrayquantUbsan.
Require OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top.BaseGrayquantBoth.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg true true true true true true.
End SpuriousCfgM.

Module HaltsCfgMayFail <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.may_fail_cfg.
End HaltsCfgMayFail.



(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_affine_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_affine_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_affine_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_affine_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_affine_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_affine_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_barcode_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_barcode_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_barcode_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_barcode_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_barcode_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_barcode_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_bilateral_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_bilateral_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_bilateral_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_bilateral_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_bilateral_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_bilateral_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_bilinear_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_bilinear_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_bilinear_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_bilinear_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_bilinear_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_bilinear_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_blend_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_blend_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_blend_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_blend_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_blend_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_blend_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_boxfunc4_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_boxfunc4_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_boxfunc4_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_boxfunc4_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_boxfunc4_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_boxfunc4_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_ccbord_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_ccbord_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_ccbord_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_ccbord_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_ccbord_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_ccbord_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_checkerboard_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_checkerboard_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_checkerboard_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_checkerboard_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_checkerboard_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_checkerboard_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_colorfill_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_colorfill_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_colorfill_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_colorfill_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_colorfill_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_colorfill_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_edge_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_edge_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_edge_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_edge_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_edge_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_edge_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_fhmtgen_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_fhmtgen_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_fhmtgen_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_fhmtgen_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_fhmtgen_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_fhmtgen_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_flipdetect_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_flipdetect_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_flipdetect_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_flipdetect_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_flipdetect_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_flipdetect_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_fpix2_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_fpix2_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_fpix2_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_fpix2_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_fpix2_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_fpix2_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_graphics_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_graphics_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_graphics_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_graphics_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_graphics_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_graphics_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_graymorph_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_graymorph_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_graymorph_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_graymorph_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_graymorph_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_graymorph_fuzzer_both_bound_diff : Q := 1%Q.


Theorem strong_universal_error_free_grayquant_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Asan.M.loaded_segments OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Asan.M.init_pc OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top.BaseGrayquantAsan.strong_universal_error_free_grayquant_fuzzer_asan.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_grayquant_fuzzer_asan_bound_good : Q := 0%Q.


(* [comment removed for export] *)
Definition b_grayquant_fuzzer_asan_bound_diff : Q := 0%Q.


Theorem strong_universal_error_free_grayquant_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.M.loaded_segments OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.M.init_pc OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Ubsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top.BaseGrayquantUbsan.strong_universal_error_free_grayquant_fuzzer_ubsan.
Qed.


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_grayquant_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_grayquant_fuzzer_ubsan_bound_diff : Q := 1%Q.


Theorem strong_universal_error_free_grayquant_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.loaded_segments OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.init_pc OssFuzzTheorems.leptonica.grayquant_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.leptonica.grayquant_fuzzer.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.leptonica.grayquant_fuzzer.images.AsanUbsan.M.init_pc OssFuzzTheorems.leptonica.grayquant_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Top.BaseGrayquantBoth.strong_universal_error_free_grayquant_fuzzer_both.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_grayquant_fuzzer_both_bound_good : Q := 0%Q.


(* [comment removed for export] *)
Definition b_grayquant_fuzzer_both_bound_diff : Q := 0%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_jpegiostub_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_jpegiostub_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_jpegiostub_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_jpegiostub_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_jpegiostub_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_jpegiostub_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_kernel_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_kernel_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_kernel_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_kernel_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_kernel_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_kernel_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_mask_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_mask_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_mask_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_mask_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_mask_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_mask_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_maze_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_maze_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_maze_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_maze_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_maze_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_maze_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_morph_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_morph_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_morph_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_morph_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_morph_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_morph_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_paintcmap_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_paintcmap_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_paintcmap_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_paintcmap_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_paintcmap_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_paintcmap_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix1_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix1_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix1_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix1_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix1_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix1_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix_orient_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix_orient_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix_orient_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix_orient_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix_orient_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix_orient_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix_rotate_shear_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix_rotate_shear_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix_rotate_shear_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix_rotate_shear_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pix_rotate_shear_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pix_rotate_shear_fuzzer_both_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pixconv_fuzzer_asan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pixconv_fuzzer_asan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pixconv_fuzzer_ubsan_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pixconv_fuzzer_ubsan_bound_diff : Q := 1%Q.




(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)
Definition b_pixconv_fuzzer_both_bound_good : Q := 1%Q.


(* [comment removed for export] *)
Definition b_pixconv_fuzzer_both_bound_diff : Q := 1%Q.


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


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)

