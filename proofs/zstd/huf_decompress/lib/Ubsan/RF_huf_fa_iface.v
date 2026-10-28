(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount HufPure_FseDecomp HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge Arr RunConst.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

Definition PHUF_FAST_ARGS_INIT : Z := 0x1e184.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition jt_len (src : list Z) (i : Z) : Z := Znth i src + 256 * Znth (i + 1) src.   (* [comment removed for export] *)

Definition fast_args_cells (DST dcap S DT : Z) (src : list Z) (b0 b1 b2 b3 : Z) : list cell :=
  let l1 := jt_len src 0 in let l2 := jt_len src 2 in let l3 := jt_len src 4 in
  let seg := (dcap + 3) / 4 in
  [ C8 (Z_to_bv 64 (S + 6 + l1 - 8)); C8 (Z_to_bv 64 (S + 6 + l1 + l2 - 8)); C8 (Z_to_bv 64 (S + 6 + l1 + l2 + l3 - 8));
    C8 (Z_to_bv 64 (S + zlen src - 8));
    C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 (DST + seg)); C8 (Z_to_bv 64 (DST + 2 * seg)); C8 (Z_to_bv 64 (DST + 3 * seg));
    C8 (Z_to_bv 64 b0); C8 (Z_to_bv 64 b1); C8 (Z_to_bv 64 b2); C8 (Z_to_bv 64 b3);
    C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 (DST + dcap));
    C8 (Z_to_bv 64 (S + 6)); C8 (Z_to_bv 64 (S + 6 + l1)); C8 (Z_to_bv 64 (S + 6 + l1 + l2));
    C8 (Z_to_bv 64 (S + 6 + l1 + l2 + l3)) ].

Definition fast_args_ok (m : fmem) (A DST dcap S DT : Z) (src : list Z) (tl : Z) : Prop :=
  tl = 11
  /\ 10 <= zlen src
  /\ 8 <= jt_len src 0 /\ 8 <= jt_len src 2 /\ 8 <= jt_len src 4
  /\ jt_len src 0 + jt_len src 2 + jt_len src 4 + 6 + 8 <= zlen src
  /\ 0 < dcap /\ 3 * ((dcap + 3) / 4) < dcap
  /\ exists b0 b1 b2 b3 : Z,
       0 <= b0 < 2^64 /\ 0 <= b1 < 2^64 /\ 0 <= b2 < 2^64 /\ 0 <= b3 < 2^64
       /\ b0 mod 512 <> 0 /\ b1 mod 512 <> 0 /\ b2 mod 512 <> 0 /\ b3 mod 512 <> 0
       /\ rw_cells usegs m A (fast_args_cells DST dcap S DT src b0 b1 b2 b3).

Definition fast_args_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A DST dcap S DT : Z) (src : list Z) (tl lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z) (m' : fmem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (A, A + 152)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ (exists ja', rw_cells usegs m' A [CB 152 ja'])
    /\ (r = 0 \/ r = 2^64 - 20 \/ (r = 1 /\ fast_args_ok m' A DST dcap S DT src tl)).

Definition fast_args_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (A DST dcap S DT mtl tt tl mtl' : Z) (src : list Z) (ja : list byte) (lo : Z),
  rw_cells usegs m A [CB 152 ja] -> A mod 8 = 0 ->
  bytes_at usegs m DT [Z_to_bv 8 mtl; Z_to_bv 8 tt; Z_to_bv 8 tl; Z_to_bv 8 mtl'] ->
  0 <= mtl < 256 -> 0 <= tt < 256 -> 0 <= tl < 256 -> 0 <= mtl' < 128 ->
  bytes_at usegs m S (map (Z_to_bv 8) src) -> Forall (fun c => 0 <= c < 256) src ->
  zlen src < 2^26 -> 0 < S ->
  0 <= DST -> 0 <= dcap < 2^32 -> DST + dcap + 8 <= 2^64 -> (0 < dcap -> 0 < DST) ->
  0 < DT -> DT mod 4 = 0 -> DT + 4 <= lo -> S + zlen src <= lo ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp <= A -> A + 152 <= 2^64 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 dcap -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 (zlen src) ->
  a5 = Z_to_bv 64 DT ->
  evt usegs (fast_args_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A DST dcap S DT src tl lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_FAST_ARGS_INIT) fc None m (seg_rom usegs)).
End CANSEC1.
