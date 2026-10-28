(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase Stdio_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_fa_iface.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).

Definition AHUF_FAST_ARGS_INIT : Z := 0x95eb0.
Definition AHUF_FAST_ARGS_STACK : Z := 48.        (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition fast_args_okA (m : amem) (A DST dcap S DT : Z) (src : list Z) (tl : Z) : Prop :=
  tl = 11
  /\ 10 <= zlen src
  /\ 8 <= jt_len src 0 /\ 8 <= jt_len src 2 /\ 8 <= jt_len src 4
  /\ jt_len src 0 + jt_len src 2 + jt_len src 4 + 6 + 8 <= zlen src
  /\ 0 < dcap /\ 3 * ((dcap + 3) / 4) < dcap
  /\ exists b0 b1 b2 b3 : Z,
       0 <= b0 < 2^64 /\ 0 <= b1 < 2^64 /\ 0 <= b2 < 2^64 /\ 0 <= b3 < 2^64
       /\ b0 mod 512 <> 0 /\ b1 mod 512 <> 0 /\ b2 mod 512 <> 0 /\ b3 mod 512 <> 0
       /\ rw_cells bsegs m A (fast_args_cells DST dcap S DT src b0 b1 b2 b3).

Definition fast_args_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A DST dcap S DT : Z) (src : list Z) (tl lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - AHUF_FAST_ARGS_STACK, bv_unsigned sp); (A, A + 152)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ (exists ja', rw_cells bsegs m' A [CB 152 ja'])
    /\ (r = 0 \/ r = 2^64 - 20 \/ (r = 1 /\ fast_args_okA m' A DST dcap S DT src tl)).

Definition fast_args_stmtA : Prop :=
  forall (RNG : footprint) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (A DST dcap S DT mtl tt tl mtl' : Z) (src : list Z) (ja : list byte)
         (lo : Z) (rstk : region),
  rw_cells bsegs m A [CB 152 ja] -> A mod 8 = 0 ->
  bytes_at bsegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl'] ->
  0 <= mtl < 256 -> 0 <= tt < 256 -> 0 <= tl < 256 -> 0 <= mtl' < 128 ->
  bytes_at bsegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
  zlen src < 2^26 -> 0 < S ->
  0 <= DST -> (0 < dcap -> 0 < DST) -> 0 <= dcap < 2^32 -> DST + dcap + 8 <= 2^64 ->
  0 < DT -> DT mod 8 = 0 -> DT + 4 <= lo -> (0 < zlen src -> S + zlen src <= lo) ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AHUF_FAST_ARGS_STACK -> ATOP + 4096 <= lo ->
  bv_unsigned sp <= A -> A + 152 <= 2^47 ->
  mem_inv bsegs m -> artcells m ->
  (* [comment removed for export] *)
  unpoisoned m DT (DT + 4) -> (0 < zlen src -> unpoisoned m S (S + zlen src)) ->
  rclean m rstk -> r_lo rstk <= A -> A + 152 <= r_hi rstk ->
  (* [comment removed for export] *)
  rng RNG (bv_unsigned sp - AHUF_FAST_ARGS_STACK) AHUF_FAST_ARGS_STACK -> rng RNG A 152 -> rrng RNG rstk ->
  rng RNG DT 4 -> rng RNG (shad DT) 1 ->
  (0 < zlen src -> rng RNG S (zlen src) /\ rng RNG (shad S) (nshad (zlen src + S mod 8))) ->
  rng_aimg RNG ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 dcap -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 (zlen src) ->
  a5 = Z_to_bv 64 DT ->
  evtF bsegs RNG (fast_args_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A DST dcap S DT src tl lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 AHUF_FAST_ARGS_INIT) fc None m (seg_rom bsegs)).
End CANSEC1.
