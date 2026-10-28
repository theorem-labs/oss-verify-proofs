(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.LinuxProcessSem.Run.
Require OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.
Require OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Asan.
Require OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.AsanUbsan.
Require OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require FinAgreeA.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require FinAgreeB.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib Require FinAgreeU.

Theorem strong_universal_error_free_speexdec_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.loaded_segments OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.init_pc OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Asan.M.loaded_segments OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Asan.M.init_pc OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Asan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.FinAgreeA.asan_agree.
Qed.

Theorem strong_universal_error_free_speexdec_fuzzer_both :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.loaded_segments OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.init_pc OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.AsanUbsan.M.init_pc OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.AsanUbsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.FinAgreeB.both_agree.
Qed.

Theorem strong_universal_error_free_speexdec_fuzzer_ubsan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets_abort
    (LinuxProcessSemantics.LinuxProcessSem.Run.alloc_only_cfg false)
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.loaded_segments OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.init_pc OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Ubsan.M.loaded_segments OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Ubsan.M.init_pc OssFuzzTheorems.speex.speex_decode_fuzzer_float.images.Ubsan.M.phdrs).
Proof.
exact OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.FinAgreeU.ubsan_agree.
Qed.
