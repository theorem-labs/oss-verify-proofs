(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AMalloc_iface AFake_iface AHarness_iface ADriver_iface AInstance AInstanceM AInstanceF ATsafeMain AMain_asm AMain_closed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
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

Section CANSEC1. Context {rc : runConstT}.
Section WithFree.
Hypothesis FREE : afree_stmt aci_I AHEAP_I.
Hypothesis FUZZ : fuzz_oneA_stmt (AI_of FREE) AFake_iface.afake_rng.
#[using="FREE FUZZ"] Theorem adrv_of_free : adrv_stmt ATsafeMain.A0.
Proof.
exact (adrv (AI_of FREE) (AI_of_E FREE) (AI_of_CI_OK FREE) (AI_of_DRV_CI FREE) (AI_of_CLI_CI FREE) FUZZ).
Qed.
End WithFree.
End CANSEC1.
Theorem asan_impl_of_free :
forall FREE : (forall rc : runConstT, afree_stmt aci_I AHEAP_I),
(forall rc : runConstT, fuzz_oneA_stmt (AI_of (FREE rc)) AFake_iface.afake_rng) -> asan_impl_stmt ASTAGE.
Proof.
intros FREE FUZZ.
exact (asan_impl ATsafeMain.NMAX ATsafeMain.A0
(fun rc : runConstT => @adrv_of_free rc (FREE rc) (FUZZ rc))
(fun rc : runConstT => @model_ok rc)
ATsafeMain.A0_init).
Qed.
