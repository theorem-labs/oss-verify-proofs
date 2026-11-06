(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require Plain.
From OSSVerify.speex.speex_decode_fuzzer_float.images Require AsanUbsan.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require Import TopE TopSides.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib Require PSide.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X19v X0w6.

Notation imgS := (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs) (only parsing).
Notation imgB := (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs) (only parsing).

Theorem HB_closed : side_canon Tc imgB target_alloc_limit.
Proof. exact (B.X19v.A_side B.X0w6.MAIN_B (fun inp Hv ok => run_defined_of_valid inp ok Hv)). Qed.

Theorem both_agree : strong_universal_error_free_T_scfg_budgets_abort (alloc_only_cfg false)
  SanitizerBudgets.lim_source SanitizerBudgets.lim_target imgS imgB.
Proof.
exact (glue_budgets_abort_at Tc imgS imgB SanitizerBudgets.lim_source SanitizerBudgets.lim_target
  PSide.P_side_closed_sanitizer HB_closed Tc_nokill).
Qed.
