(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run MemImageType.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Plain.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BsonPmFinal.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import IcptIfaceA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import LibIfaceAB HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import Ba0MainPhaseA_b BatIfaceInst_b BatIfaceLayoutPM_b
     Ba0InstA_b Ba0InstAX_b Ba0DiagArms_b Ba0UsageArm_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmLayoutA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PnLayoutA_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStaticsA PnStaticsA. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import PmSpecsA_b PnSpecsAa_b PnAHarnessStmts_b PnAHarness_b PnALibOk_b PnALayFacts_b
     PnAImgGap_b PnSpecsAmc_b BatIfaceMcmp_b PnRunA_b PnRunAa_b PnAResetBStmts_b PnAClosePkg_b PnACloseRd_b PnACloseRs_b BsonPmAsanTop_b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pkg_stmt : Prop :=
  forall ar HIR, HAJ.asan_iface_okR art_L ar art_C cfg0 HIR -> aicpt_ok art_L ar art_IL cfg0 HIR -> HAJ.asan_ext_ok art_L ar cfg0 HIR PMA.EXT ->
    PMAGAP.rt_img_gap HIR -> @PNHA.harness_depsA ScfgP_cfg0 art_L ar HIR.

(* [comment removed for export] *)
Definition holes_stmt : Prop :=
  (forall ar HIR, @PNACP.inst_ok ScfgP_cfg0 art_L art_C art_IL ar HIR -> @PNRAa.reader_ctor_spec ScfgP_cfg0 art_L ar HIR)
  /\ (forall ar HIR, @PNACP.inst_ok ScfgP_cfg0 art_L art_C art_IL ar HIR -> @PNARBS.reset_spec ScfgP_cfg0 art_L ar HIR)
  /\ (forall ar HIR, @PNACP.inst_ok ScfgP_cfg0 art_L art_C art_IL ar HIR -> @PNRAa.parse_spec ScfgP_cfg0 art_L ar HIR).
Lemma pkg_of_holes : holes_stmt -> pkg_stmt.
Proof.
  intros (R1 & R2 & R3).
  exact (@PNACP.pkg ScfgP_cfg0 art_L art_C art_IL art_pma_layout art_IL_ok BatIfaceMcmp_b.art_mcmp_cells R1 R2 R3).
Qed.

(* [comment removed for export] *)
Definition parse_stmt : Prop :=
  forall ar HIR, @PNACP.inst_ok ScfgP_cfg0 art_L art_C art_IL ar HIR -> @PNRAa.parse_spec ScfgP_cfg0 art_L ar HIR.
Lemma pkg_of_parse : parse_stmt -> pkg_stmt.
Proof.
  intros R3. apply pkg_of_holes. split; [|split; [|exact R3]].
  - exact (@PNACR.reader_ctor_closed ScfgP_cfg0 art_L art_C art_IL art_pma_layout art_IL_ok BatIfaceMcmp_b.art_mcmp_cells).
  - exact (@PNACRS.reset_closed ScfgP_cfg0 art_L art_C art_IL art_pma_layout).
Qed.

(* [comment removed for export] *)
Lemma ba0_inst : inst_ok_stmt cfg0 art_L art_C BUDGET0.           Proof. exact (as0_inst_ok cfg0 BUDGET0 eq_refl). Qed.
Lemma ba0_free_null : free_null_stmt cfg0 art_L BUDGET0.           Proof. exact (as0_free_null cfg0 BUDGET0). Qed.
Lemma ba0_h4e : h4e_stmt BUDGET0.                                  Proof. exact (as0_h4e BUDGET0). Qed.
Lemma ba0_icpt : icpt_ok_stmt cfg0 art_L art_IL BUDGET0.           Proof. exact (as0_icpt_ok cfg0 art_IL BUDGET0 art_IL_ok). Qed.
Lemma ba0_ext : ext_ok_stmt cfg0 art_L PMA.EXT BUDGET0.            Proof. exact (as0_ext_ok_pma cfg0 BUDGET0 eq_refl). Qed.
Lemma ba0_gap : gap_ok_stmt BUDGET0.                               Proof. exact (as0_gap_ok BUDGET0). Qed.
Lemma ba0_dla : dla_ok_stmt cfg0 art_L art_C art_IL.               Proof. exact (as0_dla_ok cfg0 art_IL art_IL_ok). Qed.
Lemma ba0_consts : drv_consts_stmt art_L art_C art_IL.             Proof. exact (as0_drv_consts art_IL art_IL_ok). Qed.
Lemma ba0_drv : drv_main_stmt cfg0 art_L art_C art_IL (PNHA.LayA art_L) (fun _ => PNSTA.TopLSA AsanUbsan.M.loaded_segments PMA.AD PMA.AAD PMA.AN).
Proof. exact (as0_drv_main_closed cfg0 art_L art_C art_IL (PNHA.LayA art_L) _ pm_lib_layout pm_lib_cells pm_lib_budget). Qed.
Lemma ba0_usage : usage_stmt cfg0.
Proof. exact (as0_usage_closed cfg0 art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi ba0_inst ba0_free_null ba0_h4e ba0_icpt ba0_dla ba0_consts). Qed.

Section Rows.
Hypothesis PKG : pkg_stmt.

(* [comment removed for export] *)
Lemma ba0_tgt : as0_tgt_stmt cfg0.
Proof.
  exact (as0_tgt_modulo art_L art_C art_IL BUDGET0 BUDGET0_lo BUDGET0_hi art_pma_layout PKG
           ba0_inst ba0_free_null ba0_h4e ba0_icpt ba0_ext ba0_gap ba0_dla ba0_consts ba0_drv ba0_usage).
Qed.

(* [comment removed for export] *)
Theorem bson_pm_asan_base :
  strong_universal_error_free_T_scfg cfg0
    (mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.phdrs).
Proof. exact (bson_pm_asan_final_scfg ba0_tgt). Qed.

(* [comment removed for export] *)
Theorem bson_pm_asan_base_abort :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.Plain.M.phdrs)
    (mkImage OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.loaded_segments OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.init_pc OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images.AsanUbsan.M.phdrs).
Proof. exact (bson_pm_asan_final_abort ba0_tgt). Qed.
End Rows.
