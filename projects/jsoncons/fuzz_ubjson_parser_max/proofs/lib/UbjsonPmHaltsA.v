(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import AsanAcct HeapIfaceA IcptIfaceA LibIfaceAJ HeapIfaceAJx AsanInitK Ja0DefsK Ja0MainPhaseA JatIfaceInst JatIfaceLayoutPM
PmLayoutA PmStaticsA PmSpecsAX PmSpecsAa PmAHarnessStmts PmAStaticsTop PmAImgGap PmALibOk PmAClose PmALayFacts
UbjsonPmFinal UbjsonPmAsanTop UbjsonPmAsanRows UbjsonPmAsanBase.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape MustExitSpec MustExitHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import UbjsonPmHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Lemma as0_top : UbjsonPmAsanTop.as0_tgt_stmt cfg0.
Proof.
assert (ILY : as0_icpt_layout art_IL) by exact (proj1 ja0_consts).
pose proof (@PMALO.lib_ok ScfgP_cfg0 art_L art_C art_IL art_pma_layout ILY (ja0_pkg leaves_ab)) as H4.
apply as0_tgt_of_run.
intros sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs.
exact (as0_realizes_spec_run cfg0 eq_refl eq_refl art_L art_C art_IL (PMHAS.Lay art_L)
(fun _ => PMSTA.TopLSA Asan.M.loaded_segments PMA.AD PMA.AAD)
PMA.EXT BUDGET0 BUDGET0_lo BUDGET0_hi ja0_inst ja0_free_null ja0_h4e ja0_icpt ja0_ext ja0_gap H4 ja0_dla ja0_consts ja0_drv ja0_usage
PMSTT.lsx_atexit
sp brk0 mbase rdraw argv envp fs stdin uid gid hw groups net nofile sigmask abrt urnd Hsp Hbrk Hva Hve Hfit Huid Hhw Hvfs).
Qed.
Lemma top_asan_closed : top_asan cfg0 target_alloc_limit.
Proof. exact as0_top. Qed.
Theorem ubjson_pm_halts_asan :
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Asan.M.loaded_segments Asan.M.init_pc
Asan.M.phdrs).
Proof. exact (ubjson_pm_halts_asan_of_top cfg0 target_alloc_limit lim_source_le_target top_asan_closed). Qed.
End FPX_1.
