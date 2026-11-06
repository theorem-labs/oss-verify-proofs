(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Plain.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Asan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopE TopSides.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require PSide.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require X0je X059.

Notation imgS := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgA := (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs) (only parsing).

Theorem HA_closed : side_canon Tc imgA target_alloc_limit.
Proof. exact (A.X0je.A_side A.X059.MAIN_A (fun inp Hv ok => run_defined_of_valid inp ok Hv)). Qed.

Theorem asan_agree : strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false)
  SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgS imgA.
Proof.
exact (glue_budgets_abort_at Tc imgS imgA SanitizerBudgets.lim_source SanitizerBudgets.lim_target
  PSide.P_side_closed_sanitizer HA_closed Tc_nokill).
Qed.
