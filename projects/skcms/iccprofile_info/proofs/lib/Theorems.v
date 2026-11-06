(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
Require OSSVerify.skcms.iccprofile_info.images.Plain.
Require OSSVerify.skcms.iccprofile_info.images.Asan.
Require OSSVerify.skcms.iccprofile_info.images.Ubsan.
Require OSSVerify.skcms.iccprofile_info.images.AsanUbsan.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Require OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoTop.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require InfoAsanClosed.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require InfoBothClosed.




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


Theorem strong_universal_error_free_fuzz_iccprofile_info_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.skcms.iccprofile_info.images.Plain.M.loaded_segments OSSVerify.skcms.iccprofile_info.images.Plain.M.init_pc OSSVerify.skcms.iccprofile_info.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.skcms.iccprofile_info.images.Asan.M.loaded_segments OSSVerify.skcms.iccprofile_info.images.Asan.M.init_pc OSSVerify.skcms.iccprofile_info.images.Asan.M.phdrs).
Proof.
exact OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan.InfoAsanClosed.info_asan_closed.
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


Theorem strong_universal_error_free_fuzz_iccprofile_info_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.skcms.iccprofile_info.images.Plain.M.loaded_segments OSSVerify.skcms.iccprofile_info.images.Plain.M.init_pc OSSVerify.skcms.iccprofile_info.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.skcms.iccprofile_info.images.Ubsan.M.loaded_segments OSSVerify.skcms.iccprofile_info.images.Ubsan.M.init_pc OSSVerify.skcms.iccprofile_info.images.Ubsan.M.phdrs).
Proof.
exact (LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_of_scfg _ _ _ OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.ProofInfoTop.info_ubsan).
Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


(* [comment removed for export] *)


Theorem strong_universal_error_free_fuzz_iccprofile_info_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.skcms.iccprofile_info.images.Plain.M.loaded_segments OSSVerify.skcms.iccprofile_info.images.Plain.M.init_pc OSSVerify.skcms.iccprofile_info.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.skcms.iccprofile_info.images.AsanUbsan.M.loaded_segments OSSVerify.skcms.iccprofile_info.images.AsanUbsan.M.init_pc OSSVerify.skcms.iccprofile_info.images.AsanUbsan.M.phdrs).
Proof.
exact OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan.InfoBothClosed.info_both_closed.
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

