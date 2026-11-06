(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg Spec BigintSpec HeapIface LibIface L5Defs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.CJ.Bridge Require Import HeapInst0 HeapClosed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import Js0DrvLibL Js0DrvG Js0DrvMain Js0HeapBridge PmTopS PmSExitCells UbjsonPmFinal UbjsonPmPkgs.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape MustExitSpec MustExitHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import UbjsonPmHalts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require PropExec.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FPX_1.
#[local] Existing Instance PropExec.fx0.
Lemma src_top : Js0DrvMain.src_realizes_stmt2 cfg0.
Proof.
exact (src0_realizes_spec_heap cfg0 eq_refl eq_refl
(fun sp => PMTS.TopLay (HeapInst0.L0 (bv_unsigned sp))) (fun _ => PMTS.TopLS)
drv_lib_layout_top0 (LIB0_of_packages packages_src) (fun sp _ => PMSXC.top_lsx) budget0).
Qed.
Lemma top_plain_closed : top_plain cfg0 source_alloc_limit.
Proof.
intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds _ _.
exact (src_top sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds).
Qed.
Theorem ubjson_pm_halts_plain :
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source halts_codes
(mkImage Plain.M.loaded_segments Plain.M.init_pc
Plain.M.phdrs).
Proof. exact (ubjson_pm_halts_plain_of_top cfg0 source_alloc_limit lim_source_le_source top_plain_closed). Qed.
End FPX_1.
