(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Zlib_iface Z_zrd Z_irep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_itab.

Module Zlib_defl_closed.
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import RefDeflSafeFB.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Zlib_iface Drv_kit Z_zrd Z_trees_iface Z_defl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_tr_fb11 Z_tr_fbubsan Z_trees_closed Z_cbound Z_dinit Z_deflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_dinit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Z_fw.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_defl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_iface.Z_tr_bt_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fb11 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_tr_fbubsan OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_trees_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_cbound OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dinit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_dinit.Z_dend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_fw.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma tr_flush_block_E_of_U : tr_flush_block_stmtU -> tr_flush_block_stmtE.
Proof.
  intros SU. unfold tr_flush_block_stmtE. intros until m. intros DR MI RC STK LO AL BEL BI FBS FE.
  apply (SU L s buf len last lo); try assumption. exact (flush_ubsan_facts s last FE buf len).
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem zlib_defl_of : fill_window_stmt -> tr_init_stmt -> tr_flush_block_stmtE -> tr_flush_bits_stmt ->
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
Proof. exact (zlib_defl_of fill_window_spec tr_init_closed (tr_flush_block_E_of_U tr_flush_block_finalU) tr_flush_bits_closed). Qed.
End WithCeiling0.
End Zlib_defl_closed.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Zlib_infl_closed.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_irep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab_kit.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Z_itab OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_closed.Zlib_defl_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U.Zlib_infl_closed.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition zR : zreps :=
  mkZreps Z_zrd.zr_d Z_irep.zr_i_def Z_zrd.zr_d_frame Z_irep.zr_i_def_frame Z_zrd.zr_d_stream Z_irep.zr_i_def_stream.

Theorem zlib_closed : zlib_ok zR.
Proof.
  destruct (zlib_defl_closed zR eq_refl) as (CB & DI & DD & DE).
  destruct (zlib_infl_closed zR eq_refl) as (II & INF & IE).
  unfold zlib_ok. repeat split; assumption.
Qed.

End WithCeiling0.

Theorem zlib_closed_all : forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_ok CE__ RN__ (@zR CE__).
Proof. intros. apply zlib_closed. Qed.
