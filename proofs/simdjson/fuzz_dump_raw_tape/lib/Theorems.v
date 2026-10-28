(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
Require OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.
Require OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Asan.
Require OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.TopClosed_asan.
Require OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Ubsan.
Require OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.TopClosed_ubsan.

Require OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.AsanUbsan.
Require OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.TopClosed_both.

Theorem fuzz_dump_raw_tape_asan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.loaded_segments
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.init_pc
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Asan.M.loaded_segments
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Asan.M.init_pc
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Asan.M.phdrs).
Proof. exact OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.TopClosed_asan.base_asan_cfg. Qed.

Theorem fuzz_dump_raw_tape_ubsan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.loaded_segments
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.init_pc
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Ubsan.M.loaded_segments
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Ubsan.M.init_pc
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Ubsan.M.phdrs).
Proof. exact OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.TopClosed_ubsan.base_ubsan_cfg. Qed.

Theorem fuzz_dump_raw_tape_both_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.loaded_segments
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.init_pc
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.AsanUbsan.M.loaded_segments
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.AsanUbsan.M.init_pc
             OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images.AsanUbsan.M.phdrs).
Proof. exact OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.TopClosed_both.base_both_cfg. Qed.
