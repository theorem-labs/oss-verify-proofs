(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List.
Require LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require LinuxProcessSemantics.EquivalenceDefinition.MustExit.
Require LinuxProcessSemantics.EquivalenceDefinition.FinInput.
Require LinuxProcessSemantics.EquivalenceDefinition.Classifier.
Require LinuxProcessSemantics.EquivalenceDefinition.Measure.
Require LinuxProcessSemantics.EquivalenceDefinition.PatchClassifySpec.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType StackLayout Fs State Run.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Plain.
Require OSSVerify.yajl_ruby.json_fuzzer.images.Asan.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling PropExec MState Mem Cells Frame Arr Nodes NodesCfg InitMem RunInit Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts ExecA LazyModel NodesA ImplRzA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim StdioBase Stdio.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import
  AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanFakeStack AsanPS AsanRep AsanKern AsanClient AsanBudget AsanBudget2 AsanDepot AsanGap AsanSlack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import
  A_base A_alloc_iface A_iface A_iface5x AF_unwind AF_fakestack_rep A_live A_policy5 A_budget5 A_slack5 A_bundle A_benv5 A_init5 A_instD5 A_inst5 ADrv_ctx ADrv_A ADrv_E
  AF_alloc_iface AF_free_iface AF_mallocT2 AF_reallocT AF_freeT2 AF_dput_iface.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require AF_deallocT2 AF_deallocT3 AF_deallocT5 AF_dputT.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import SpecT GlueCfg RunInitCfg R_TopCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require RA_EquivCfg RU_FinalCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Clf Require ClfTop.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.TopA Require A_TopCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Theorem strong_universal_error_free_json_fuzzer_asan :
  LinuxProcessSemantics.EquivalenceDefinition.Equivalence.strong_universal_error_free_T_scfg_budgets
    SpuriousCfgM.cfg
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_source
    LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets.lim_target
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Plain.M.phdrs)
    (LinuxProcessSemantics.LinuxProcessSem.MemImageType.mkImage OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.loaded_segments OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.init_pc OSSVerify.yajl_ruby.json_fuzzer.images.Asan.M.phdrs).
Proof.
  (* [comment removed for export] *)
  exact (RA_EquivCfg.strong_universal_error_free_json_fuzzer_asan_budgets RU_FinalCfg.R_realizes_spec_final_2G A_TopCfg.A_realizes_spec_cfg).
Qed.
