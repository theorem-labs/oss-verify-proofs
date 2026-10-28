(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib Require Import TopLevel Obligations ProofBase TopLevelA TopFinal_plain TopFinal_asan.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Plain.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Asan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_rep RT_sys_fixed RT_refill D_client TopB_final El_defsA El_clrecA El_dumpA.
Require OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P.El_client_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.

Lemma client_P_closed : client_P_stmt.
Proof. intros CE RN. exact (@OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P.El_client_closed.rfuzz_one_closed CE RN). Qed.

Theorem s3s_asan_closed : S3s_stmt_e Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs.
Proof. exact (s3s_both (client_el (refill_ok fixed_commit_ok) el_dump) client_el_hs). Qed.

Theorem off_asan :
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true)
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (TopFinal_asan.off_asan_cfg client_P_closed s3s_asan_closed). Qed.
Theorem base_asan :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage Asan.M.loaded_segments Asan.M.init_pc Asan.M.phdrs).
Proof. exact (TopFinal_asan.base_asan_cfg client_P_closed s3s_asan_closed). Qed.
