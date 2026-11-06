(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct HeapIfaceA IcptIfaceAB0 LibIfaceAJ HeapIfaceAJx AsanInitK Jb0DefsK Jb0MainPhaseA JbtIfaceInst JbtIfaceLayoutPM
PmLayoutA PmStaticsA PmSpecsAX PmSpecsAb PmBHarnessStmts PmBStaticsTop PmBImgGap PmBLibOk PmBClose PmBLayFacts
UbjsonPmFinal UbjsonPmBothTop UbjsonPmBothRows UbjsonPmBothBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape MustExitSpec MustExitHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import UbjsonPmHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Lemma bo0_top : UbjsonPmBothTop.as0_tgt_stmt cfg0.
Proof.
assert (ILY : as0_icpt_layout art_IL) by exact (proj1 jb0_consts).
pose proof (@PMBLO.lib_ok ScfgP_cfg0 art_L art_C art_IL art_pma_layout ILY (jb0_pkg leaves_ab)) as H4.
apply as0_tgt_of_run.
intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
exact (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL (PMHAS.Lay art_L)
(fun _ => PMSTA.TopLSA AsanUbsan.M.loaded_segments PMB.AD PMB.AAD)
PMB.EXT BUDGET0 BUDGET0_lo BUDGET0_hi jb0_inst jb0_free_null jb0_h4e jb0_icpt jb0_ext jb0_gap H4 jb0_dla jb0_consts jb0_drv jb0_usage
PMSTTB.lsx_atexit
sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs).
Qed.
Lemma top_both_closed : top_both cfg0 target_alloc_limit.
Proof. exact bo0_top. Qed.
Theorem ubjson_pm_halts_both :
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage AsanUbsan.M.loaded_segments AsanUbsan.M.init_pc
AsanUbsan.M.phdrs).
Proof. exact (ubjson_pm_halts_both_of_top cfg0 target_alloc_limit lim_source_le_target top_both_closed). Qed.
End FPX_1.
