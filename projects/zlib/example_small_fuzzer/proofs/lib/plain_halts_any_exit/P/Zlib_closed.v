(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Rnd Zlib_iface Z_zrd Z_irep Z_infl_iface Z_itab.

Module Zlib_defl_closed.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Zlib_iface Drv_kit Z_zrd Z_trees_iface Z_defl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_trees_closed Z_cbound Z_dinit Z_deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_dinit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_fw.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_trees_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_cbound OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dinit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_dinit.Z_dend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_fw.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem zlib_defl_of : fill_window_stmt -> tr_init_stmt -> tr_flush_block_stmt -> tr_flush_bits_stmt ->
  forall R : zreps, Zlib_iface.zr_d R = Z_zrd.zr_d ->
  compressBound_stmt /\ deflateInit_stmt R /\ deflate_stmt R /\ deflateEnd_stmt R.
Proof.
  intros HFW HTRI HTFBLK HTFB R ER. split; [|split; [|split]].
  - exact compressBound_proof.
  - exact (deflateInit_proof rmalloc_spec rfree_spec_proof RHEAP_blocks_nodup_proof RHEAP_block_range_proof RHEAP_blocks_disjoint_proof RHEAP_frame_proof HTRI R ER).
  - exact (deflate_proof HFW HTFBLK HTFB R ER).
  - exact (deflateEnd_proof rfree_spec_proof RHEAP_blocks_nodup_proof RHEAP_block_range_proof RHEAP_frame_proof R ER).
Qed.

Theorem zlib_defl_closed :
  forall R : zreps, Zlib_iface.zr_d R = Z_zrd.zr_d ->
  compressBound_stmt /\ deflateInit_stmt R /\ deflate_stmt R /\ deflateEnd_stmt R.
Proof. exact (zlib_defl_of fill_window_spec tr_init_closed tr_flush_block_final tr_flush_bits_closed). Qed.
End WithCeiling0.
End Zlib_defl_closed.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Zlib_infl_closed.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Rnd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_irep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_itab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_closed.Zlib_defl_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_infl_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition zR : zreps :=
  mkZreps Z_zrd.zr_d Z_irep.zr_i_def Z_zrd.zr_d_frame Z_irep.zr_i_def_frame Z_zrd.zr_d_stream Z_irep.zr_i_def_stream.

Theorem zlib_closed_of_itable : Z_infl_iface.inflate_table_stmt -> zlib_ok zR.
Proof.
  intros IT.
  destruct (zlib_defl_closed zR eq_refl) as (CB & DI & DD & DE).
  destruct (zlib_infl_of_itable IT zR eq_refl) as (II & INF & IE).
  unfold zlib_ok. repeat split; assumption.
Qed.

Theorem zlib_closed : zlib_ok zR.
Proof. exact (zlib_closed_of_itable Z_itab.inflate_table_proof). Qed.

End WithCeiling0.

Theorem zlib_closed_all : forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_ok CE__ RN__ (@zR CE__).
Proof. intros. apply zlib_closed. Qed.
