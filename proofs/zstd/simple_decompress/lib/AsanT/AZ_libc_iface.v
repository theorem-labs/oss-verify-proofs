(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Notation APZD_MEMSET := 0x53ca0 (only parsing).
Notation APZD_MEMCPY := 0x53804 (only parsing).
Notation APZD_MEMMOVE := 0x53ee0 (only parsing).
Notation MEMSET_STACK_A := 2208 (only parsing).
Notation MEMCPY_STACK_A := 2224 (only parsing).
Notation MEMMOVE_STACK_A := 2224 (only parsing).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_memsetZ_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPz A n c lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPz - MEMSET_STACK_A, SPz); (A, A + n)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPz
    /\ rw_cells bsegs m' A [CB (Z.to_nat n) (repeat (Z_to_bv 8 c) (Z.to_nat n))].

Definition zd_memsetZ_stmtA : Prop :=
  forall (RNG : footprint) (A n c SPz : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (junk : list byte),
  rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
  0 <= n <= 2^40 -> 0 <= c < 256 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMSET_STACK_A -> SPz < 2^47 -> (A + n <= lo \/ SPz <= A) ->
  (* [comment removed for export] *)
  app_blk A (A + n) -> aro RNG m A n -> ahull RNG m A n -> art m -> astk RNG lo SPz ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 c -> a2 = Z_to_bv 64 n ->
  evtF bsegs RNG (zd_memsetZ_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz A n c lo m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMSET) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_memcpyZ_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPz A S n lo : Z) (src : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPz - MEMCPY_STACK_A, SPz); (A, A + n)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPz
    /\ rw_cells bsegs m' A [CB (Z.to_nat n) src]
    /\ bytes_at bsegs m' S src.

Definition zd_memcpyZ_stmtA : Prop :=
  forall (RNG : footprint) (A S n SPz : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (src junk : list byte),
  bytes_at bsegs m S src -> length src = Z.to_nat n ->
  rw_cells bsegs m A [CB (Z.to_nat n) junk] ->
  (S + n <= A \/ A + n <= S) ->
  0 <= n <= 2^40 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMCPY_STACK_A -> SPz < 2^47 ->
  (S + n <= SPz - MEMCPY_STACK_A \/ SPz <= S) -> (A + n <= lo \/ SPz <= A) ->
  (* [comment removed for export] *)
  app_blk S (S + n) -> aro RNG m S n -> ahull RNG m S n -> app_blk A (A + n) -> aro RNG m A n -> ahull RNG m A n ->
  art m -> astk RNG lo SPz ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  evtF bsegs RNG (zd_memcpyZ_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz A S n lo src m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMCPY) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_memmoveZ_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPz D n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(SPz - MEMMOVE_STACK_A, SPz); (D, D + n)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPz
    /\ stk bsegs m' D (D + n).

Definition zd_memmoveZ_stmtA : Prop :=
  forall (RNG : footprint) (D S n SPz : Z) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z),
  stk bsegs m D (D + n) -> rdbl bsegs m S (S + n) ->
  0 <= n <= 2^40 ->
  stk bsegs m lo SPz -> lo <= SPz - MEMMOVE_STACK_A -> SPz < 2^47 ->
  (S + n <= SPz - MEMMOVE_STACK_A \/ SPz <= S) -> (D + n <= lo \/ SPz <= D) ->
  (* [comment removed for export] *)
  app_blk S (S + n) -> aro RNG m S n -> ahull RNG m S n -> app_blk D (D + n) -> aro RNG m D n -> ahull RNG m D n ->
  art m -> astk RNG lo SPz ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 n ->
  evtF bsegs RNG (zd_memmoveZ_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPz D n lo m)
    (MS (mkR ra (Z_to_bv 64 SPz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 APZD_MEMMOVE) fc None m (seg_rom bsegs)).
End CANSEC1.
