(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling RzCPS Cfg.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevel Obligations ProofBase TopLevelA TopFinal_plain TopFinal_both.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Zks Zkt RT_rep Z7w Z11g Z45 Z4e Z3z.
Require OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Rnd OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Z41.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma client_P_closed : client_P_stmt.
Proof. intros CE RN. exact (@OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P.Z41.rfuzz_one_closed CE RN). Qed.

Theorem s3s_both_closed : S3s_stmt_e AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc AsanUbsan.M.phdrs.
Proof. exact (Z11g.s3s_both client_atp client_atp_hs). Qed.

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
