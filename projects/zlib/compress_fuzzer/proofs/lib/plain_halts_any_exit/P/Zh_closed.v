(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ITree Nodes.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Monad Stdio Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface RMalloc_ifaceP RCalloc_iface RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Stdio_iface Printf_stdio_iface Printf_closed Zlib_iface Drv_kit Z_cbound
  Zc_iface Zc_compress2 Zc_uncompress2 Zc_uncompress Zc_fuzz.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rfuzz_one_of_zlib : forall R : zreps, zlib_okC R -> rcalloc_stmt -> rfuzz_oneC_stmt.
Proof.
  intros R ZOK CALLOC.
  pose proof (compress2_proof R ZOK RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof) as C2.
  pose proof (uncompress2_proof R ZOK RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof) as U2.
  pose proof (uncompress_proof U2 RHEAP_frame_proof RHEAP_block_range_proof) as UNC.
  exact (fz_main compressBound_proof CALLOC rmalloc_spec rfree_spec_proof C2 UNC
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.
End WithCeiling0.
