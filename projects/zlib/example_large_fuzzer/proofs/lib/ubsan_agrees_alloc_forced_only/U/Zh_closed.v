(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ITree Nodes.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Monad Stdio Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocU Require Import RMalloc_iface RMalloc_ifaceP RCalloc_iface RF_free_spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Stdio_iface Printf_stdio_iface Printf_closed F_towrite F_fwrite Zlib_iface Zl_iface Drv_kit Zl_stderr Zl_h_deflate Zl_h_inflate Zl_h_fuzz.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rfuzz_one_of_zlib : forall R : zrepsL, zlib_okL R -> rcalloc_stmt -> rfuzz_oneL_stmt.
Proof.
  intros R ZOK CALLOC.
  pose proof (@check_err_proof PState fwritex_stderr_ok stdio_write_flush_ok) as CHK.
  pose proof (@bad_msg_proof PState fwritex_stderr_ok stdio_write_flush_ok) as BAD.
  pose proof (@fwrite_diag_proof PState towrite_proof) as FWR.
  exact (fz_mainL CALLOC rfree_spec_proof
           (rtest_large_deflate_proof R ZOK CHK FWR RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof)
           (rtest_large_inflate_proof R ZOK CHK BAD RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof)
           RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof).
Qed.
End WithCeiling0.
