(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling RzCPS Cfg.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib Require Import TopLevel Obligations ProofBase TopLevelA TopFinal_plain TopFinal_both.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import Plain.
From OssFuzzTheorems.simdjson.fuzz_dump.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import RT_iface RT_iface2 RT_rep D_client TopB_final El_defsA Dmp_clrecA Dmp_pj_closedA.
Require OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P.Dmp_client_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A.Shadow.GWf.

Lemma client_P_closed : client_P_stmt.
Proof. intros CE RN. exact (@OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P.Dmp_client_closed.rfuzz_one_closed CE RN). Qed.

Theorem s3s_both_closed : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. exact (s3s_both client_dmp_closed client_dmp_hs). Qed.

Theorem off_both_cfg :
  strong_universal_error_free_T_scfg ACFG
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (TopFinal_both.off_both_cfg client_P_closed s3s_both_closed). Qed.
Theorem base_both_cfg :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true)
    SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (TopFinal_both.base_both_cfg client_P_closed s3s_both_closed). Qed.
