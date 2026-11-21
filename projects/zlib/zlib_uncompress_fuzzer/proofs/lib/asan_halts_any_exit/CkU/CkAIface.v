(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.CkU Require Import CkAImg CkATables CkAShadow.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Notation amem := (word -> option byte).

Definition CK_CRC32Z_STACK  : Z := 144.
Definition CK_COMBINE_STACK : Z := 16.
Definition CK_GEN_STACK     : Z := 16.
Definition CK_ADLER32Z_STACK : Z := 160.
Definition CK_FUZZ_STACK    : Z := 272.


Definition ck_postA (FRAME : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (FR : bvmap 5 word) (fc : bv 32) (res : Z) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - FRAME, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp).

Definition ck_leaf_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (FR : bvmap 5 word) (fc : bv 32) (res : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 res) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m (seg_rom asegs).

Notation ck_entry pc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m :=
  (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      FR (Z_to_bv 64 pc) fc None m (seg_rom asegs)).


Definition crc32_z_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (c A : Z) (bs : list Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_CRC32Z_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> ck_sh m ->
  a0 = Z_to_bv 64 c -> 0 <= c < 2^64 ->
  a1 = Z_to_bv 64 A -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  ck_buf RNG m A bs ->
  rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_CRC32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (crc32_z_model A c bs) lo m)
       (ck_entry ACK_CRC32Z ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition crc32_z_null_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_CRC32Z_STACK -> KHIGH <= lo ->
  a1 = Z_to_bv 64 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_CRC32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc 0 lo m)
       (ck_entry ACK_CRC32Z ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition crc32_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (c A v : Z) (bs : list Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_CRC32Z_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> ck_sh m ->
  a0 = Z_to_bv 64 c -> 0 <= c < 2^64 ->
  a1 = Z_to_bv 64 A -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  a2 = Z_to_bv 64 v -> 0 <= v < 2^64 -> v mod 2^32 = Z.of_nat (length bs) ->
  ck_buf RNG m A bs ->
  rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_CRC32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (crc32_z_model A c bs) lo m)
       (ck_entry ACK_CRC32 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition crc32_null_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_CRC32Z_STACK -> KHIGH <= lo ->
  a1 = Z_to_bv 64 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_CRC32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc 0 lo m)
       (ck_entry ACK_CRC32 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).


Definition crc32_combine_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (crc1 crc2 len2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_COMBINE_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> ck_sh m ->
  a0 = Z_to_bv 64 crc1 -> a1 = Z_to_bv 64 crc2 -> a2 = Z_to_bv 64 len2 ->
  0 <= crc1 < 2^32 -> 0 <= crc2 < 2^64 -> 0 <= len2 < 2^63 ->
  rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_COMBINE_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (crc32_combine crc1 crc2 len2) lo m)
       (ck_entry ACK_COMBINE ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition crc32_combine_gen_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (len2 : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_GEN_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> ck_sh m ->
  a0 = Z_to_bv 64 len2 -> 0 <= len2 < 2^63 ->
  rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_GEN_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (crc32_combine_gen len2) lo m)
       (ck_entry ACK_GEN ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition crc32_combine_op_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (crc1 crc2 op : Z),
  a0 = Z_to_bv 64 crc1 -> a1 = Z_to_bv 64 crc2 -> a2 = Z_to_bv 64 op ->
  0 <= crc1 < 2^32 -> 0 <= crc2 < 2^64 -> 0 <= op < 2^64 -> op mod 2^32 <> 0 ->
  evtF asegs RNG (ck_leaf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (crc32_combine_op crc1 crc2 op) m)
       (ck_entry ACK_OP ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).


Definition adler32_z_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (adler A : Z) (bs : list Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_ADLER32Z_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 adler -> 0 <= adler < 2^64 ->
  a1 = Z_to_bv 64 A -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  a2 = Z_to_bv 64 (Z.of_nat (length bs)) ->
  ck_buf RNG m A bs ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_ADLER32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (adler32_z_model adler bs) lo m)
       (ck_entry ACK_ADLER32Z ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition adler32_z_null_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_ADLER32Z_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_ADLER32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc 1 lo m)
       (ck_entry ACK_ADLER32Z ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition adler32_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (adler A v : Z) (bs : list Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_ADLER32Z_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  a0 = Z_to_bv 64 adler -> 0 <= adler < 2^64 ->
  a1 = Z_to_bv 64 A -> 1 <= A -> A + Z.of_nat (length bs) <= lo ->
  a2 = Z_to_bv 64 v -> 0 <= v < 2^64 -> v mod 2^32 = Z.of_nat (length bs) ->
  ck_buf RNG m A bs ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_ADLER32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (adler32_z_model adler bs) lo m)
       (ck_entry ACK_ADLER32 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition adler32_null_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_ADLER32Z_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m ->
  a1 = Z_to_bv 64 0 -> a2 = Z_to_bv 64 0 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_ADLER32Z_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc 1 lo m)
       (ck_entry ACK_ADLER32 ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition adler32_combine_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (ad1 ad2 len2 : Z),
  mem_inv asegs m ->
  a0 = Z_to_bv 64 ad1 -> a1 = Z_to_bv 64 ad2 -> a2 = Z_to_bv 64 len2 ->
  0 <= ad1 < 2^64 -> 0 <= ad2 < 2^64 -> 0 <= len2 < 2^63 ->
  rng_aimg RNG ->
  evtF asegs RNG (ck_leaf_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (adler32_combine_model ad1 ad2 len2) m)
       (ck_entry ACK_ADLCOMB ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).

Definition ck_fuzz_stmtA : Prop :=
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (D n : Z),
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - CK_FUZZ_STACK -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> ck_sh m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  (1 <= n <= 2^20 -> exists bs, Z.of_nat (length bs) = n /\ ck_buf RNG m D bs /\ 1 <= D /\ D + n <= lo) ->
  rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA CK_FUZZ_STACK ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc 0 lo m)
       (ck_entry ACK_FUZZ ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m).
