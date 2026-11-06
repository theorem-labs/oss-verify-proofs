(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require OSSVerify.glaze.binary_reflection.images.Plain.
Require OSSVerify.glaze.binary_reflection.images.Asan.
Require OSSVerify.glaze.binary_reflection.images.Ubsan.
Require OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.DrvRootP.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvRootP.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsBaseA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.TopProof5.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoBaseB.

Theorem strong_universal_error_free_binary_reflection_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.glaze.binary_reflection.images.Plain.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Plain.M.init_pc OSSVerify.glaze.binary_reflection.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.glaze.binary_reflection.images.Asan.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Asan.M.init_pc OSSVerify.glaze.binary_reflection.images.Asan.M.phdrs).
Proof.
  exact (TopProof5.asan_base_of_san DrvRootP.P_root_holds AsBaseA.A_root_closed).
Qed.

Theorem strong_universal_error_free_binary_reflection_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.glaze.binary_reflection.images.Plain.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Plain.M.init_pc OSSVerify.glaze.binary_reflection.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.glaze.binary_reflection.images.Ubsan.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Ubsan.M.init_pc OSSVerify.glaze.binary_reflection.images.Ubsan.M.phdrs).
Proof.
  exact (TopProof4.ubsan_base_of DrvRootP.P_root_holds UbDrvRootP.U_root_holds).
Qed.

Theorem strong_universal_error_free_binary_reflection_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.glaze.binary_reflection.images.Plain.M.loaded_segments OSSVerify.glaze.binary_reflection.images.Plain.M.init_pc OSSVerify.glaze.binary_reflection.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.loaded_segments OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.init_pc OSSVerify.glaze.binary_reflection.images.AsanUbsan.M.phdrs).
Proof.
  exact (TopProof5.both_base_of_san DrvRootP.P_root_holds BoBaseB.B_root_closed).
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
