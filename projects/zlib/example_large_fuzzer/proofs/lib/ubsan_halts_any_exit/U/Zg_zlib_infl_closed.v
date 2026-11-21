(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.U Require Import Zlib_iface Drv_kit Z_irep Z_infl_iface Zg_infl_iface Z_infl_t_iface Zg_infl_t_iface Z_infl_defs Zg_infl_defs Zg_zlib_iface Zg_updwin_iface
  Zg_infl_arms Zg_infl_arms_have Zg_inflate_ok Z_iinit Z_iend Z_itab Zg_adler32 Zg_updwin Zg_inffast.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import InflateState InflateArms Inflate.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
  Let ARMS : arms_okg 0 :=
    arms_okg_of 0 ltac:(lia) inflate_table_proof inflate_fast_g adler32_g.

  Theorem inflate_proofG : forall R : zreps, zr_i R = zr_i_def -> inflate_stmtG R.
  Proof.
    intros R ER.
    exact (inflate_okG rmalloc_spec RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof
             ARMS adler32_g updwin_have_g updwin_ret_block_g R ER).
  Qed.

  Theorem zlib_infl_closedG : forall R : zreps, zr_i R = zr_i_def ->
    inflateInit_stmt R /\ inflate_stmtG R /\ inflateEnd_stmt R.
  Proof.
    intros R ER. split; [|split].
    - exact (inflateInit_ok rmalloc_spec RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof R ER).
    - exact (inflate_proofG R ER).
    - exact (inflateEnd_ok rfree_spec_proof RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof R ER).
  Qed.

End WithCeiling0.
