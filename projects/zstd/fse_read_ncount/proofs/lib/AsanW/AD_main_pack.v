(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import ITree Nodes InitMem RunConst.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import Prelim STree Monad Stdio Driver Adapter Prog AsanCtrl AsanEmbed Harness ProgA AsanProgDeps AsanHandoff.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase AProto AMalloc_iface AProg_kit AHarness_iface Strnlen_iface ADriver_iface AD_main AMain_asm.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section Packed.
Variable AI : AMallocIface.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
Hypothesis CI_WF : forall iv, In iv (aci AI) -> 0 <= fst iv.
Hypothesis DMALLOC : dmalloc_stmt AI.
Hypothesis DFREE : dfree_stmt AI.
Hypothesis DFREEN : dfree_null_stmt AI.
Hypothesis ASHENV : ashenv_law AI.
Hypothesis FUZZ : fuzz_oneA_stmt AI rng_fs.
Hypothesis HSTRN : strnlen_a_stmt.
#[using="rng_fs_mono DRV_CI CLI_CI CI_WF DMALLOC DFREE DFREEN ASHENV FUZZ HSTRN"] Corollary adrv_of_walks : forall (A0 : (nat -> Z) -> alw),
(forall en inp w V m ms mo,
valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> amain_open en inp w V m ms mo ->
atop_of (en_sp en) = ATOP ->
exists L, apat_mainA AI rng_fs L (RNG0 A0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms) ->
adrv_stmt A0.
Proof.
intros A0 APAT. apply (adrv_of_parts A0 (apat_mainA AI rng_fs) APAT).
intros L RNG inp s0 ms HP. eapply amain_packed; eassumption.
Qed.
End Packed.
End CANSEC1.
