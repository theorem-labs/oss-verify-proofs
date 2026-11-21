(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog ZApi ZInst ZApiC ZInstC.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd Zlib_iface Drv_kit Z_zrd Z_irep Z_trees_iface Z_trees_closed Zg_zlib_iface Zg_zlib_infl_closed
  Zg_dinit_ifaceG Zg_dinitG Zg_defl_iface2 Zg_defl_closed2 Zc_zrd Zc_iface Zc_deflate Zc_dapi Zc_iend.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition zR : zreps :=
  mkZreps Zc_zrd.zr_dC Z_irep.zr_i_def Zc_zrd.zr_dC_frame Z_irep.zr_i_def_frame Zc_zrd.zr_dC_stream Z_irep.zr_i_def_stream.

Theorem zlib_closed : zlib_okC zR.
Proof.
  destruct (zlib_infl_closedG zR eq_refl) as (II & INF & _).
  unfold zlib_okC. split; [| split; [| split; [| split; [exact II| split; [exact INF|]]]]].
  - exact (deflateInit_proofC (deflateInit_proofG rmalloc_spec rfree_spec_proof RHEAP_blocks_nodup_proof RHEAP_block_range_proof
                                 RHEAP_blocks_disjoint_proof RHEAP_frame_proof tr_init_closed) zR eq_refl).
  - exact (deflate_proofC deflate_in_g2 zR eq_refl).
  - exact (deflateEnd_proofC rfree_spec_proof RHEAP_blocks_nodup_proof RHEAP_block_range_proof RHEAP_frame_proof zR eq_refl).
  - exact (inflateEnd_okX rfree_spec_proof RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof zR eq_refl).
Qed.

End WithCeiling0.

Theorem zlib_closed_all : forall (CE__ : Ceiling) (RN__ : RunRnd), @zlib_okC CE__ RN__ (@zR CE__).
Proof. intros. apply zlib_closed. Qed.
