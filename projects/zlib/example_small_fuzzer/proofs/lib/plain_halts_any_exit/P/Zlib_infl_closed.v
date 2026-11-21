(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Zlib_iface Drv_kit Z_irep Z_infl_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_defs2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_infl_arms_have Z_inflate_ok Z_iinit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_iinit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Z_itab.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_irep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_defs2.Z_infl_arms OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_infl_arms_have OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_inflate_ok OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_iinit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_iinit.Z_iend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Z_itab.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Theorem zlib_infl_of_arms : arms_ok 0 -> forall R : zreps, zr_i R = zr_i_def ->
  inflateInit_stmt R /\ inflate_stmt R /\ inflateEnd_stmt R.
Proof.
  intros ARMS R ER. split; [|split].
  - exact (inflateInit_ok rmalloc_spec RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof R ER).
  - exact (inflate_ok rmalloc_spec RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof ARMS R ER).
  - exact (inflateEnd_ok rfree_spec_proof RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof R ER).
Qed.

Theorem zlib_infl_of_itable : Z_infl_iface.inflate_table_stmt -> forall R : zreps, zr_i R = zr_i_def ->
  inflateInit_stmt R /\ inflate_stmt R /\ inflateEnd_stmt R.
Proof. intros IT. exact (zlib_infl_of_arms (arms_ok_0 IT)). Qed.

Theorem zlib_infl_closed : forall R : zreps, zr_i R = zr_i_def -> inflateInit_stmt R /\ inflate_stmt R /\ inflateEnd_stmt R.
Proof. exact (zlib_infl_of_itable inflate_table_proof). Qed.

Definition zreps_with_infl (zd : mem -> Z -> list block -> DS the_zapi -> Prop)
    (Fd : forall m m' S LBz ds, zd m S LBz ds ->
            (forall a, 0 <= a < 2^64 -> (S + ZS_PUB <= a < S + ZS_SIZEOF \/ in_block LBz a) ->
               m' (wa a) = m (wa a) /\ (wview psegs m (wa a) <> None -> wview psegs m' (wa a) <> None)) -> zd m' S LBz ds)
    (Sd : forall m S LBz ds, zd m S LBz ds -> exists j : list byte, rw_cells psegs m (S + ZS_PUB) [CB 64 j]) : zreps :=
  mkZreps zd zr_i_def Fd zr_i_def_frame Sd zr_i_def_stream.
End WithCeiling0.
