(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ITree Nodes.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Spec Require Import Monad Stdio Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMalloc_iface RMalloc_ifaceP RCalloc_iface RF_free_spec.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Stdio_iface Printf_stdio_iface Printf_closed.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require F_fwrite Zlib_iface Drv_kit Zh_stderr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Driver_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Zh_inflate.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Zh_inflate Zh_fuzz.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Printf_closed OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwritex.F_towrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.F_fwrite OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_stderr OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Driver_iface.Zh_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_inflate.Zh_deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_inflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P.Zh_fuzz.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rfuzz_one_of_zlib : forall R : zreps, zlib_ok R -> rcalloc_stmt -> rfuzz_one_stmt.
Proof.
  intros R ZOK CALLOC.
  pose proof (@check_err_proof PState fwritex_stderr_ok stdio_write_flush_ok) as CHK.
  pose proof (@fwrite_diag_proof PState towrite_proof) as FWR.
  exact (fz_main R ZOK CALLOC rfree_spec_proof rfree_null_spec
           (rtest_deflate_proof R ZOK CHK RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof)
           (rtest_inflate_proof R ZOK CHK FWR RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof)
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.
End WithCeiling0.
