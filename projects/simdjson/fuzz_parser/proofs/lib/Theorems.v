(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
Require OSSVerify.simdjson.fuzz_parser.images.Plain.
Require OSSVerify.simdjson.fuzz_parser.images.Asan.
Require OSSVerify.simdjson.fuzz_parser.images.Ubsan.
Require OSSVerify.simdjson.fuzz_parser.images.AsanUbsan.
Require OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClosedP.
Require OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.

Theorem fuzz_parser_asan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.simdjson.fuzz_parser.images.Plain.M.loaded_segments
             OSSVerify.simdjson.fuzz_parser.images.Plain.M.init_pc
             OSSVerify.simdjson.fuzz_parser.images.Plain.M.phdrs)
    (mkImage OSSVerify.simdjson.fuzz_parser.images.Asan.M.loaded_segments
             OSSVerify.simdjson.fuzz_parser.images.Asan.M.init_pc
             OSSVerify.simdjson.fuzz_parser.images.Asan.M.phdrs).
Proof. exact (OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClosedP.base_asan_mc OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.plain_client OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.asan_client). Qed.

Theorem fuzz_parser_ubsan_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage OSSVerify.simdjson.fuzz_parser.images.Plain.M.loaded_segments
             OSSVerify.simdjson.fuzz_parser.images.Plain.M.init_pc
             OSSVerify.simdjson.fuzz_parser.images.Plain.M.phdrs)
    (mkImage OSSVerify.simdjson.fuzz_parser.images.Ubsan.M.loaded_segments
             OSSVerify.simdjson.fuzz_parser.images.Ubsan.M.init_pc
             OSSVerify.simdjson.fuzz_parser.images.Ubsan.M.phdrs).
Proof. exact (OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClosedP.base_ubsan_mc OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.plain_client OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.ubsan_client). Qed.

Theorem fuzz_parser_both_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.simdjson.fuzz_parser.images.Plain.M.loaded_segments
             OSSVerify.simdjson.fuzz_parser.images.Plain.M.init_pc
             OSSVerify.simdjson.fuzz_parser.images.Plain.M.phdrs)
    (mkImage OSSVerify.simdjson.fuzz_parser.images.AsanUbsan.M.loaded_segments
             OSSVerify.simdjson.fuzz_parser.images.AsanUbsan.M.init_pc
             OSSVerify.simdjson.fuzz_parser.images.AsanUbsan.M.phdrs).
Proof. exact (OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClosedP.base_both_mc OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.plain_client OSSVerify.Proofs.simdjson.fuzz_parser.lib.ClientP.both_client). Qed.
