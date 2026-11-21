(* (uncompress 1.4 UBSan): the memset spec the I8U walks call, for this binary: musl memset at
   0x218b0 (137392) with n = 7176 (inflateInit_'s memset of the whole inflate_state, from state + 0), from
   U8Memset7176R.memset7176_run through IGlueMemset.memset_glue. The plain build's I9S/SMemsetOk.v, moved. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* a worker 2026-11-07 (uncompress 1.4 UBSan): the memset spec the I9U walks call, for this binary: musl memset at
   0x217f4 (137204) with n = 7176 (inflateInit_'s memset of the whole inflate_state, from state + 0), from
   U9Memset7176R.memset7176_run through IGlueMemset.memset_glue. The plain build's I9S/SMemsetOk.v, moved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_zlib_uncompress_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatSim Hoare ZStores.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require U9Memset U9Memset7176R.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZStep IGlueMemset.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U Require Import i9u_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Definition A_MEMSET : Z := 137300.   (* memset, 0x217f4 *)

Lemma w64_lit' : forall z (w : word), bv_unsigned w = z -> w64 z = w. Proof. intros z w <-. apply w64_of_word. Qed.

Lemma msteps_memset_U9 {RCa1 : RunCtx}  : msteps_memset (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7176.
Proof.
  intros regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok. change (Z.of_nat 7176) with 7176%Z in H12, Hnw.
  change (store_ok (run_segments R_segs rc_inp rc_sp rc_mb) mem0 dst 7176 = true) with (store_ok (run_segments R_segs rc_inp rc_sp rc_mb) mem0 dst (7 * 1024 + 8) = true) in Hok.
  destruct (U9Memset7176R.memset7176_run regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok)
    as (r' & m' & RUN & EQ & AG).
  exists r'. subst m'. split; [| exact AG]. unfold A_MEMSET, R_segs. rewrite (w64_lit' 137300 (0x21854%bv : word)) by reflexivity. exact RUN.
Qed.

Theorem memset7176_ok {RCa1 : RunCtx}  : memset_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7176.
Proof. pose proof (memset_glue (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7176 msteps_memset_U9) as G. change (Z.of_nat 7176) with 7176%Z in G. exact G. Qed.
