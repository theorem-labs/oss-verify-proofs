(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* The proofs in this file are Anthropic's; the theorem statements were issued by the task authors and are reproduced as issued (see NOTICE). *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Plain.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Asan Ubsan AsanUbsan.
From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.Top Require BaseFhmtgenAsan BaseFhmtgenUbsan BaseFhmtgenBoth.

Theorem fhmtgen_fuzzer_asan_agrees :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
       Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc
       Asan.M.phdrs).
Proof. exact BaseFhmtgenAsan.strong_universal_error_free_fhmtgen_fuzzer_asan. Qed.

Theorem fhmtgen_fuzzer_ubsan_agrees :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false)
    ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
       Plain.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
       Ubsan.M.phdrs).
Proof. exact BaseFhmtgenUbsan.strong_universal_error_free_fhmtgen_fuzzer_ubsan. Qed.

Theorem fhmtgen_fuzzer_asan_ubsan_agrees :
  strong_universal_error_free_T_scfg_budgets (Run.alloc_only_cfg false)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc
       Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
       AsanUbsan.M.phdrs).
Proof. exact BaseFhmtgenBoth.strong_universal_error_free_fhmtgen_fuzzer_both. Qed.
