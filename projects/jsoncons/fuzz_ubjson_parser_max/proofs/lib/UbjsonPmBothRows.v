(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Plain.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ClassifierRows UbjsonPmImgFacts UbjsonPmImgFactsB UbjsonPmFinal.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import HeapIface HeapIfaceA IcptIfaceAB0 LibIfaceAJ HeapIfaceAJx Jb0MainPhaseA JbtIfaceInst JbtIfaceLayoutPM
Jb0InstA Jb0InstAX Jb0DiagArms Jb0UsageArm PmLayoutA PmStaticsA PmSpecsAb PmBHarnessStmts PmBLibOk PmBClose PmBLayFacts
UbjsonPmBothTop UbjsonPmBothTopOld PmSpecsAmc PmBImgGap PmBLeaves JbtIfaceMcmp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition leaves_stmt : Prop :=
forall ar HIR, HAJ.asan_iface_okR art_L ar art_C cfg0 HIR -> aicpt_ok art_L ar art_IL cfg0 HIR -> HAJ.asan_ext_ok art_L ar cfg0 HIR PMB.EXT ->
PMBGAP.rt_img_gap HIR -> @PMBLV.open_leaves ScfgP_cfg0 art_L ar HIR.
Lemma jb0_inst : inst_ok_stmt cfg0 art_L art_C BUDGET0. Proof. exact (as0_inst_ok cfg0 BUDGET0 eq_refl). Qed.
Lemma jb0_free_null : free_null_stmt cfg0 art_L BUDGET0. Proof. exact (as0_free_null cfg0 BUDGET0). Qed.
Lemma jb0_h4e : h4e_stmt BUDGET0. Proof. exact (as0_h4e BUDGET0). Qed.
Lemma jb0_icpt : icpt_ok_stmt cfg0 art_L art_IL BUDGET0. Proof. exact (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok). Qed.
Lemma jb0_ext : ext_ok_stmt cfg0 art_L PMB.EXT BUDGET0. Proof. exact (as0_ext_ok_pma cfg0 BUDGET0 eq_refl). Qed.
Lemma jb0_gap : gap_ok_stmt BUDGET0. Proof. exact (as0_gap_ok BUDGET0). Qed.
Lemma jb0_dla : dla_ok_stmt cfg0 art_L art_C art_IL. Proof. exact (as0_dla_ok cfg0 art_IL art_IL_ok). Qed.
Lemma jb0_consts : drv_consts_stmt art_L art_C art_IL. Proof. exact (as0_drv_consts art_IL art_IL_ok). Qed.
Lemma jb0_drv : drv_main_stmt cfg0 art_L art_C art_IL (PMHAS.Lay art_L) (fun _ => PMSTA.TopLSA AsanUbsan.M.loaded_segments PMB.AD PMB.AAD).
Proof. exact (as0_drv_main_closed cfg0 art_L art_C art_IL (PMHAS.Lay art_L) _ pm_lib_layout pm_lib_cells pm_lib_budget). Qed.
Lemma jb0_usage : usage_stmt cfg0.
Proof. exact (as0_usage_closed cfg0 art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi jb0_inst jb0_free_null jb0_h4e jb0_icpt jb0_dla jb0_consts). Qed.
Section Rows.
Hypothesis LEAVES : leaves_stmt.
Lemma jb0_pkg : forall ar HIR, HAJ.asan_iface_okR art_L ar art_C cfg0 HIR -> aicpt_ok art_L ar art_IL cfg0 HIR -> HAJ.asan_ext_ok art_L ar cfg0 HIR PMB.EXT ->
PMBGAP.rt_img_gap HIR -> @PMBLO.harness_depsB ScfgP_cfg0 art_L ar HIR.
Proof.
intros ar HIR OK IC EX GP.
exact (@PMBLV.deps_of_leaves ScfgP_cfg0 art_L ar art_C art_IL HIR art_pma_layout OK IC art_IL_ok EX JbtIfaceMcmp.art_mcmp_cells GP (LEAVES ar HIR OK IC EX GP)).
Qed.
Theorem ubjson_pm_both_base :
strong_universal_error_free_T_scfg cfg0
(mkImage OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.phdrs)
(mkImage OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.init_pc OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.phdrs).
Proof.
exact (ubjson_pm_both_base_scfg_modulo art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi art_pma_layout jb0_pkg
jb0_inst jb0_free_null jb0_h4e jb0_icpt jb0_ext jb0_gap jb0_dla jb0_consts jb0_drv jb0_usage).
Qed.
Theorem ubjson_pm_both_base_abort :
strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
(mkImage OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Plain.M.phdrs)
(mkImage OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.init_pc OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.phdrs).
Proof.
exact (ubjson_pm_both_base_abort_modulo art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi art_pma_layout jb0_pkg
jb0_inst jb0_free_null jb0_h4e jb0_icpt jb0_ext jb0_gap jb0_dla jb0_consts jb0_drv jb0_usage).
Qed.
End Rows.
