(* the memset spec the I8U walks call, for this binary: musl memset at
   0x218b0 (137392) with n = 7176 (inflateInit_'s memset of the whole inflate_state, from state + 0), from
   U8Memset7176R.memset7176_run through IGlueMemset.memset_glue. The plain build's I9S/SMemsetOk.v, moved. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx. (* the memset spec the I7U walks call, for this binary: musl memset at
   0x21820 (137248) with n = 7176 (inflateInit_'s memset of the whole inflate_state, from state + 0), from
   U7Memset7176R.memset7176_run through IGlueMemset.memset_glue. The plain build's I9S/SMemsetOk.v, moved. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import Tgt_zlib_uncompress2_fuzzer_ubsan.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatSim Hoare ZStores.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require U7Memset U7Memset7176R.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZStep IGlueMemset.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require Import i7u_code.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Definition A_MEMSET : Z := 137332.   (* memset, 0x21820 *)

Lemma w64_lit' : forall z (w : word), bv_unsigned w = z -> w64 z = w. Proof. intros z w <-. apply w64_of_word. Qed.

Lemma msteps_memset_U7 {RCa1 : RunCtx}  : msteps_memset (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7176.
Proof.
  intros regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok. change (Z.of_nat 7176) with 7176%Z in H12, Hnw.
  change (store_ok (run_segments R_segs rc_inp rc_sp rc_mb) mem0 dst 7176 = true) with (store_ok (run_segments R_segs rc_inp rc_sp rc_mb) mem0 dst (7 * 1024 + 8) = true) in Hok.
  destruct (U7Memset7176R.memset7176_run regs mem0 rom dst ret H1 Hret H10 H11 H12 Hal Hnw Hok)
    as (r' & m' & RUN & EQ & AG).
  exists r'. subst m'. split; [| exact AG]. unfold A_MEMSET, R_segs. rewrite (w64_lit' 137332 (0x21874%bv : word)) by reflexivity. exact RUN.
Qed.

Theorem memset7176_ok {RCa1 : RunCtx}  : memset_spec_at (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7176.
Proof. pose proof (memset_glue (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMSET 7176 msteps_memset_U7) as G. change (Z.of_nat 7176) with 7176%Z in G. exact G. Qed.
