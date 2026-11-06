(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ImgParams MainDefs MainTree MainAsm Img_src13 AsanTopU AsanMainU.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import RunConst.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import ADriver_iface.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require AMain_finalX.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require BudgetBridge.
Section Final.
  Variable CS : certs IP_src13.
  Theorem base_asan :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
      (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
      LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.simdjson.fuzz_utf8.images.Plain.M.loaded_segments OSSVerify.simdjson.fuzz_utf8.images.Plain.M.init_pc OSSVerify.simdjson.fuzz_utf8.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.simdjson.fuzz_utf8.images.Asan.M.loaded_segments OSSVerify.simdjson.fuzz_utf8.images.Asan.M.init_pc OSSVerify.simdjson.fuzz_utf8.images.Asan.M.phdrs).
  Proof. apply BudgetBridge.sue_scfg_abort_shipped_to_sanitizer. exact (AsanMainU.base (PLAIN CS) NOKILL SPEC_nil ASTAGE AMain_finalX.asan_impl_closed). Qed.
  Theorem base_asan_plain :
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg
      (LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.simdjson.fuzz_utf8.images.Plain.M.loaded_segments OSSVerify.simdjson.fuzz_utf8.images.Plain.M.init_pc OSSVerify.simdjson.fuzz_utf8.images.Plain.M.phdrs)
      (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.simdjson.fuzz_utf8.images.Asan.M.loaded_segments OSSVerify.simdjson.fuzz_utf8.images.Asan.M.init_pc OSSVerify.simdjson.fuzz_utf8.images.Asan.M.phdrs).
  Proof.
    intros enS enT inp HvS HvT Hvi0.
    pose proof (valid_input_either_of_valid_input _ Hvi0) as Hvi.
    destruct (PLAIN CS enS inp HvS Hvi) as [HtrS HerrS].
    destruct (AsanMainU.target_side SPEC_nil ASTAGE AMain_finalX.asan_impl_closed enT inp HvT Hvi) as [HtrT HerrT].
    split; [exact HerrS|]. split; [exact HerrT|].
    intros tr. split; intros H; [exact (proj2 (HtrT tr) (proj1 (HtrS tr) H)) | exact (proj2 (HtrS tr) (proj1 (HtrT tr) H))].
  Qed.
End Final.
