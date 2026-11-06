(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations ProofBase TopLevelA TopFinal_plain TopFinal_asan TopClosed_plain.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Asan.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import RT_iface RT_iface2 RT_rep TopA_io TopA_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.

Theorem s3s_asan_closed : S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof. exact (TopA_final.s3s_asan TopA_io.main_rta). Qed.

Theorem off_asan :
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true)
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (TopFinal_asan.off_asan_cfg TopClosed_plain.client_P_closed s3s_asan_closed). Qed.
Theorem base_asan :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (TopFinal_asan.base_asan_cfg TopClosed_plain.client_P_closed s3s_asan_closed). Qed.
