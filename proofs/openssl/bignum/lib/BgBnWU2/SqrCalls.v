(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import Tac Arr.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import BnBase BnWords BgWords.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnTacX BnMem.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgBnW Require Import W_mul_normal.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnWU Require Import BnUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition sqr_comba4_spec (CS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z),
    limbs a -> length a = 4%nat ->
    limbs_at bgusegs m (bv_unsigned a1) a ->
    wr_at bgusegs m (bv_unsigned a0) 64 ->
    (bv_unsigned a0 + 64 <= bv_unsigned a1 \/ bv_unsigned a1 + 32 <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS)%Z ->
    (bv_unsigned a0 + 64 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 32 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) ->
    evt bgusegs (vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 8 CS (sqr_comba4 a) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x106eac) fc None m (seg_rom bgusegs)).

Definition sqr_comba8_spec (CS : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (a : list Z) (lo : Z),
    limbs a -> length a = 8%nat ->
    limbs_at bgusegs m (bv_unsigned a1) a ->
    wr_at bgusegs m (bv_unsigned a0) 128 ->
    (bv_unsigned a0 + 128 <= bv_unsigned a1 \/ bv_unsigned a1 + 64 <= bv_unsigned a0)%Z ->
    stk bgusegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - CS)%Z ->
    (bv_unsigned a0 + 128 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
    (bv_unsigned a1 + 64 <= bv_unsigned sp - CS \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
    mem_inv bgusegs m ->
    ub_ptr_ok 1 (bv_unsigned a0) -> ub_ptr_ok 1 (bv_unsigned a1) ->
    evt bgusegs (vl_post bgusegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) 16 CS (sqr_comba8 a) lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x105af4) fc None m (seg_rom bgusegs)).
