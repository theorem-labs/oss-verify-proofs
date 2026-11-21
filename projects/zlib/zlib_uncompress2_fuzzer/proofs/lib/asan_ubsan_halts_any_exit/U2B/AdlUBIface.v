(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ADL_STACK : Z := 176.

Section CANSEC1. Context {rc : runConstT}.

Definition adl_postU (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (FR : bvmap 5 word) (fc : bv 32) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (res : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - ADL_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Definition adler32_stmtU : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (adler A v : Z) (bs : list Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ADL_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 adler -> 0 <= adler < 2^64 ->
  a1 = Z_to_bv 64 A -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  a2 = Z_to_bv 64 v -> 0 <= v < 2^64 -> v mod 2^32 = Z.of_nat (length bs) ->
  bytes_at bsegs m A (map (Z_to_bv 8) bs) -> Forall (fun b => 0 <= b < 256) bs ->
  unpoisoned m A (A + Z.of_nat (length bs)) ->
  rng RNG A (Z.of_nat (length bs)) ->
  (A < A + Z.of_nat (length bs) -> rng RNG (shad A) (shad (A + Z.of_nat (length bs) - 1) + 1 - shad A)) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (adl_postU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 A_ADLER32) fc None m (seg_rom bsegs)).

Definition adler32_null_stmtU : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ADL_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
       ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                FR (ret_pc ra) fc None m' (seg_rom bsegs)
       /\ munch [(bv_unsigned sp - ADL_STACK, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
       /\ stk bsegs m' lo (bv_unsigned sp))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 A_ADLER32) fc None m (seg_rom bsegs)).
End CANSEC1.
