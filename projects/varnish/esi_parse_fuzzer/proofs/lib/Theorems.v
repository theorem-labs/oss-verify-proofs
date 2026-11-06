(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List QArith.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.varnish.esi_parse_fuzzer.images.Plain.
Require OSSVerify.varnish.esi_parse_fuzzer.images.Asan.
Require OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.
Require OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.
Require OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_Top.
Require OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yt.E_TopA.
Require OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zt.E_TopB.

Theorem strong_universal_error_free_esi_parse_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Ubsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.E_Top.strong_universal_error_free_esi_parse_fuzzer_ubsan.
Qed.

Theorem strong_universal_error_free_esi_parse_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Asan.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Asan.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Asan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yt.E_TopA.asan_budgets.
Qed.

Theorem strong_universal_error_free_esi_parse_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.loaded_segments OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.init_pc OSSVerify.varnish.esi_parse_fuzzer.images.AsanUbsan.M.phdrs).
Proof.
  exact OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zt.E_TopB.both_budgets.
Qed.
