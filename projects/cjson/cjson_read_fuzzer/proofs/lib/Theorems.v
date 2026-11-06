(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Plain.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Asan.
Require OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.
Require OSSVerify.cjson.cjson_read_fuzzer.images.AsanUbsan.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.TopAsanClosed.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Glue.TopGlue.
Require OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.TopBothClosed.

Theorem strong_universal_error_free_cjson_read_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Asan.M.loaded_segments OSSVerify.cjson.cjson_read_fuzzer.images.Asan.M.init_pc OSSVerify.cjson.cjson_read_fuzzer.images.Asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.TopAsanClosed.asan_base_san.
Qed.

Theorem strong_universal_error_free_cjson_read_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.init_pc OSSVerify.cjson.cjson_read_fuzzer.images.Ubsan.M.phdrs).
Proof.
  apply LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_of_scfg.
  exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Glue.TopGlue.ubsan_base.
Qed.

Theorem strong_universal_error_free_cjson_read_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.loaded_segments OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.init_pc OSSVerify.cjson.cjson_read_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.cjson.cjson_read_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.cjson.cjson_read_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.cjson.cjson_read_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.TopBothClosed.both_base_san.
Qed.
