(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst1 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Ju0DrvLibL Ju0DrvG Ju0DrvMain Ju0HeapBridge PmTopU PmUExitCells UbjsonPmFinal UbjsonPmPkgs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape MustExitSpec MustExitHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import UbjsonPmHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Lemma ub_top : Ju0DrvMain.tgt_realizes_stmt2 cfg0.
Proof.
exact (ub0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTU.TopLay (HeapInst1.L1 (bv_unsigned sp))) (fun _ => PMTU.TopLS)
drv_lib_layout_top1 (LIB1_of_packages packages_ub) (fun sp _ => PMUXC.top_lsx) budget1).
Qed.
Lemma top_ubsan_closed : top_ubsan cfg0 target_alloc_limit.
Proof.
intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds _ _.
exact (ub_top sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds).
Qed.
Theorem ubjson_pm_halts_ubsan :
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc
Ubsan.M.phdrs).
Proof. exact (ubjson_pm_halts_ubsan_of_top cfg0 target_alloc_limit lim_source_le_target top_ubsan_closed). Qed.
End FPX_1.
