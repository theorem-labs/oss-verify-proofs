(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Ceiling RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_element.lib Require Import TopLevel Obligations ProofBase TopLevelA TopFinal_plain TopFinal_both.
From OSSVerify.simdjson.fuzz_element.images Require Import Plain.
From OSSVerify.simdjson.fuzz_element.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import RT_iface RT_iface2 RT_rep RT_sys_fixed RT_refill D_client TopB_final El_defsA El_clrecA El_dumpA.
Require OSSVerify.Proofs.simdjson.fuzz_element.lib.P.El_client_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance OSSVerify.Proofs.simdjson.fuzz_element.lib.A.Shadow.GWf.

Lemma client_P_closed : client_P_stmt.
Proof. intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_element.lib.P.El_client_closed.rfuzz_one_closed CE RN). Qed.

Theorem s3s_both_closed : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. exact (s3s_both (client_el (refill_ok fixed_commit_ok) el_dump) client_el_hs). Qed.

Theorem off_both :
  strong_universal_error_free_T_scfg (mkSpuriousCfg false true true true true true)
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (TopFinal_both.off_both_cfg client_P_closed s3s_both_closed). Qed.
Theorem base_both :
  strong_universal_error_free_T_scfg_budgets_abort (mkSpuriousCfg false true true true true true) SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs)
    (mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs).
Proof. exact (TopFinal_both.base_both_cfg client_P_closed s3s_both_closed). Qed.
