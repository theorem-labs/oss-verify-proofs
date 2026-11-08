(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: whole copy of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/UbjsonPmHalts.v at c395a1e0dfa, with OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib renamed to OSSVerify.Proofs.jsoncons.fuzz_bigint.lib, OSSVerify.jsoncons.fuzz_ubjson_parser_max.images to OSSVerify.jsoncons.fuzz_bigint.images, Common.MustExit* to Corpus.Corpus*, and the four ubjson_pm_halts_*_of_top theorems renamed to bigint_pm_halts_*_of_top. *)
(* Modified by Theorem Labs, 2026-11: taken from ossv175b/bigint at b5b2fc487168 and adapted to this tree's srz_spin, which carries spin_site_present segs (see Corpus/CorpusSpin.v). bigint_pm_halts_plain_of_top and bigint_pm_halts_ubsan_of_top keep their statements and discharge halts_of_srealizes_top's new premise from Src0NoSpin.src0_no_spin_site and Ub0NoSpin.ub0_no_spin_site, so CorpusHaltsP.v and CorpusHaltsU.v are unchanged; bigint_pm_halts_asan_of_top and bigint_pm_halts_both_of_top take ~ spin_site_present of their image as a premise, since those images contain self-jump words and no scan can refute them. A Require of Src0NoSpin and Ub0NoSpin is added. *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg SpinAlg Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require Import CorpusShape CorpusSpec CorpusHalts.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Src0NoSpin Ub0NoSpin.
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
(* The plain and UBSan images hold no self-jump word in any read-only executable segment, so
   [srz_spin] cannot fire for them and [halts_of_srealizes_top]'s premise is discharged here from
   the byte scan of lib/Src0NoSpin.v and lib/Ub0NoSpin.v.  The two ASan images do contain self-jump
   words, so no such fact exists for them and the premise stays where their caller must supply it. *)
Theorem bigint_pm_halts_plain_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM -> top_plain cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Plain.M.loaded_segments Plain.M.init_pc
Plain.M.phdrs).
Proof. intros cfgJ LIM Hle TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle Src0NoSpin.src0_no_spin_site jspec_exits TOP). Qed.
Theorem bigint_pm_halts_ubsan_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM -> top_ubsan cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
Ubsan.M.phdrs).
Proof. intros cfgJ LIM Hle TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle Ub0NoSpin.ub0_no_spin_site jspec_exits TOP). Qed.
Theorem bigint_pm_halts_asan_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM ->
~ spin_site_present Asan.M.loaded_segments -> top_asan cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Asan.M.loaded_segments Asan.M.init_pc
Asan.M.phdrs).
Proof. intros cfgJ LIM Hle Hns TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle Hns jspec_exits TOP). Qed.
Theorem bigint_pm_halts_both_of_top : forall cfgJ LIM, ShippedBudgets.lim_source <= LIM ->
~ spin_site_present AsanUbsan.M.loaded_segments -> top_both cfgJ LIM ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
AsanUbsan.M.phdrs).
Proof. intros cfgJ LIM Hle Hns TOP. exact (halts_of_srealizes_top _ cfgJ _ _ LIM halts_codes jspec Hle Hns jspec_exits TOP). Qed.
End FPX_1.
