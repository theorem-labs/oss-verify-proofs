(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prog ZApi ZInst.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RMalloc_iface RMalloc_ifaceP RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Zlib_iface Drv_kit Z_irep Z_infl_iface Zg_infl_iface Zg_zlib_iface Zg_updwin_iface
  Zg_inflate_ok Z_iinit Z_iend Zg_inffast Zg_adler32 Zg_updwin.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Theorem inflate_proofG : forall R : zreps, zr_i R = zr_i_def -> inflate_stmtG R.
Proof.
  intros R ER.
  exact (inflate_okG rmalloc_spec RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof
           inflate_fast_proof adler32_g updwin_have_g updwin_ret_block_g R ER).
Qed.

(* [comment removed for export] *)
Theorem zlib_infl_closedG : forall R : zreps, zr_i R = zr_i_def ->
  inflateInit_stmt R /\ inflate_stmtG R /\ inflateEnd_stmt R.
Proof.
  intros R ER. split; [|split].
  - exact (inflateInit_ok rmalloc_spec RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof RHEAP_blocks_disjoint_proof R ER).
  - exact (inflate_proofG R ER).
  - exact (inflateEnd_ok rfree_spec_proof RHEAP_frame_proof RHEAP_block_range_proof RHEAP_blocks_nodup_proof R ER).
Qed.

(* [comment removed for export] *)

End WithCeiling0.
