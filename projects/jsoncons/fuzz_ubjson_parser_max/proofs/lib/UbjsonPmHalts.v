(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape MustExitSpec MustExitHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Definition jspec (inp : ProcInput) : TSet := spec (in_argv inp) (in_fs inp).
Lemma jspec_exits : forall inp, exits_in halts_codes (jspec inp).
Proof. intros inp. unfold jspec. apply exits_in_bigint_spec. Qed.
Definition top_plain (cfgJ : SpuriousCfg) (LIM : Z) : Prop :=
srealizes_top Plain.M.loaded_segments cfgJ
Plain.M.init_pc Plain.M.phdrs LIM jspec.
Definition top_ubsan (cfgJ : SpuriousCfg) (LIM : Z) : Prop :=
srealizes_top Ubsan.M.loaded_segments cfgJ
Ubsan.M.init_pc Ubsan.M.phdrs LIM jspec.
Definition top_asan (cfgJ : SpuriousCfg) (LIM : Z) : Prop :=
srealizes_top Asan.M.loaded_segments cfgJ
Asan.M.init_pc Asan.M.phdrs LIM jspec.
Definition top_both (cfgJ : SpuriousCfg) (LIM : Z) : Prop :=
srealizes_top AsanUbsan.M.loaded_segments cfgJ
AsanUbsan.M.init_pc AsanUbsan.M.phdrs LIM jspec.
Theorem ubjson_pm_halts_plain_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM -> top_plain cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Plain.M.loaded_segments Plain.M.init_pc
Plain.M.phdrs).
Proof. intros cfgJ LIM Hle TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle jspec_exits TOP). Qed.
Theorem ubjson_pm_halts_ubsan_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM -> top_ubsan cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
Ubsan.M.phdrs).
Proof. intros cfgJ LIM Hle TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle jspec_exits TOP). Qed.
Theorem ubjson_pm_halts_asan_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM -> top_asan cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Asan.M.loaded_segments Asan.M.init_pc
Asan.M.phdrs).
Proof. intros cfgJ LIM Hle TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle jspec_exits TOP). Qed.
Theorem ubjson_pm_halts_both_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM -> top_both cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
AsanUbsan.M.phdrs).
Proof. intros cfgJ LIM Hle TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle jspec_exits TOP). Qed.
End FPX_1.
