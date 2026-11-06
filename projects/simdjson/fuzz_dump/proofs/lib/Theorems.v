(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
Require OSSVerify.simdjson.fuzz_dump.images.Plain.
Require OSSVerify.simdjson.fuzz_dump.images.Asan.
Require OSSVerify.Proofs.simdjson.fuzz_dump.lib.TopClosed_asan.
Require OSSVerify.simdjson.fuzz_dump.images.Ubsan.
Require OSSVerify.Proofs.simdjson.fuzz_dump.lib.TopClosed_ubsan.

Require OSSVerify.simdjson.fuzz_dump.images.AsanUbsan.
Require OSSVerify.Proofs.simdjson.fuzz_dump.lib.TopClosed_both.

Theorem fuzz_dump_asan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.simdjson.fuzz_dump.images.Plain.M.loaded_segments
             OSSVerify.simdjson.fuzz_dump.images.Plain.M.init_pc
             OSSVerify.simdjson.fuzz_dump.images.Plain.M.phdrs)
    (mkImage OSSVerify.simdjson.fuzz_dump.images.Asan.M.loaded_segments
             OSSVerify.simdjson.fuzz_dump.images.Asan.M.init_pc
             OSSVerify.simdjson.fuzz_dump.images.Asan.M.phdrs).
Proof. exact OSSVerify.Proofs.simdjson.fuzz_dump.lib.TopClosed_asan.base_asan_cfg. Qed.

Theorem fuzz_dump_ubsan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.simdjson.fuzz_dump.images.Plain.M.loaded_segments
             OSSVerify.simdjson.fuzz_dump.images.Plain.M.init_pc
             OSSVerify.simdjson.fuzz_dump.images.Plain.M.phdrs)
    (mkImage OSSVerify.simdjson.fuzz_dump.images.Ubsan.M.loaded_segments
             OSSVerify.simdjson.fuzz_dump.images.Ubsan.M.init_pc
             OSSVerify.simdjson.fuzz_dump.images.Ubsan.M.phdrs).
Proof. exact OSSVerify.Proofs.simdjson.fuzz_dump.lib.TopClosed_ubsan.base_ubsan_cfg. Qed.

Theorem fuzz_dump_both_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.simdjson.fuzz_dump.images.Plain.M.loaded_segments
             OSSVerify.simdjson.fuzz_dump.images.Plain.M.init_pc
             OSSVerify.simdjson.fuzz_dump.images.Plain.M.phdrs)
    (mkImage OSSVerify.simdjson.fuzz_dump.images.AsanUbsan.M.loaded_segments
             OSSVerify.simdjson.fuzz_dump.images.AsanUbsan.M.init_pc
             OSSVerify.simdjson.fuzz_dump.images.AsanUbsan.M.phdrs).
Proof. exact OSSVerify.Proofs.simdjson.fuzz_dump.lib.TopClosed_both.base_both_cfg. Qed.
