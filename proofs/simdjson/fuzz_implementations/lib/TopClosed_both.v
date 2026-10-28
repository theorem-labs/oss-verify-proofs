(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Ceiling RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations ProofBase TopLevelA TopFinal_plain TopFinal_both TopClosed_plain.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import Plain.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import RT_iface RT_iface2 RT_rep TopA_io TopA_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GWf.

Theorem s3s_both_closed : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. exact (TopA_final.s3s_asan TopA_io.main_rta). Qed.

Theorem off_both :
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true)
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (TopFinal_both.off_both_cfg TopClosed_plain.client_P_closed s3s_both_closed). Qed.
Theorem base_both :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (TopFinal_both.base_both_cfg TopClosed_plain.client_P_closed s3s_both_closed). Qed.
