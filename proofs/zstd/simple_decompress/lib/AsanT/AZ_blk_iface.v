(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR .
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation BUILDFSE_STACK_A := 176 (only parsing).   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.


Definition APZD_BUILDFSE : Z := 0x88060.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition off_stack (lo SPV X n : Z) : Prop := X + n <= lo \/ SPV <= X.
(* [comment removed for export] *)
Definition apart (X n Y k : Z) : Prop := X + n <= Y \/ Y + k <= X.

(* [comment removed for export] *)

Definition zd_buildfse_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DT W : Z) (k : seq_kind) (tl : Z) (wlen : nat) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' t wb',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DT, DT + 8 + 8 * 2^tl); (W, W + Z.of_nat wlen); (SPV - BUILDFSE_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ u8arr bsegs m' DT (map (Z_to_bv 8) (seq_table_bytes t)) /\ st_log t = tl /\ seq_table_ok k t
    /\ u8arr bsegs m' W wb' /\ length wb' = wlen.

Definition zd_buildfse_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind)
         (dt0 wb0 : list byte) (norm : list Z),
  (* [comment removed for export] *)
  u8arr bsegs m DT dt0 -> Z.of_nat (length dt0) = 8 + 8 * 2^tl ->
  u8arr bsegs m W wb0 -> 626 <= Z.of_nat (length wb0) ->
  (* [comment removed for export] *)
  bytes_at bsegs m NC (u16s (map (Z_to_bv 64) norm)) ->
  5 <= tl <= kind_maxLog k -> 0 <= maxSV <= kind_max k -> maxSV + 1 <= FseNCount.Zlength norm ->
  (forall i, 0 <= i <= maxSV -> -1 <= Znth i norm) ->
  wsum (firstn (Z.to_nat (maxSV + 1)) norm) = 2^tl ->
  (* [comment removed for export] *)
  bytes_at bsegs m BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
  bytes_at bsegs m BITS (map (Z_to_bv 8) (kind_bits k)) ->
  (* [comment removed for export] *)
  4096 <= DT -> DT + 8 + 8 * 2^tl < 2^47 -> 4096 <= W -> W + Z.of_nat (length wb0) < 2^47 ->
  4096 <= NC -> NC + 2 * FseNCount.Zlength norm < 2^47 -> 4096 <= BASE < 2^47 -> 4096 <= BITS < 2^47 ->
  stk bsegs m lo SPV -> lo <= SPV - BUILDFSE_STACK_A -> 0 <= lo -> 0 <= SPV < 2^47 ->
  off_stack lo SPV DT (8 + 8 * 2^tl) -> off_stack lo SPV W (Z.of_nat (length wb0)) ->
  off_stack lo SPV NC (2 * FseNCount.Zlength norm) -> off_stack lo SPV BASE 212 -> off_stack lo SPV BITS 53 ->
  apart DT (8 + 8 * 2^tl) W (Z.of_nat (length wb0)) ->
  apart DT (8 + 8 * 2^tl) NC (2 * FseNCount.Zlength norm) -> apart W (Z.of_nat (length wb0)) NC (2 * FseNCount.Zlength norm) ->
  apart DT (8 + 8 * 2^tl) BASE 212 -> apart DT (8 + 8 * 2^tl) BITS 53 ->
  apart W (Z.of_nat (length wb0)) BASE 212 -> apart W (Z.of_nat (length wb0)) BITS 53 ->
  (* [comment removed for export] *)
  areg RNG m DT (8 + 8 * 2^tl) -> areg RNG m W (Z.of_nat (length wb0)) -> areg RNG m NC (2 * FseNCount.Zlength norm) ->
  aro RNG m BASE (4 * Z.of_nat (length (kind_base k))) -> aro RNG m BITS (Z.of_nat (length (kind_bits k))) -> art m -> astk RNG lo SPV ->
  BASE + 212 <= 2^47 -> BITS + 53 <= 2^47 ->
  (* [comment removed for export] *)
  DT mod 4 = 0 -> W mod 2 = 0 -> NC mod 2 = 0 -> BASE mod 4 = 0 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DT -> a1 = Z_to_bv 64 NC -> a2 = Z_to_bv 64 maxSV -> a3 = Z_to_bv 64 BASE -> a4 = Z_to_bv 64 BITS ->
  a5 = Z_to_bv 64 tl -> a6 = Z_to_bv 64 W ->
  evtF bsegs RNG (zd_buildfse_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W k tl (length wb0) lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_BUILDFSE) fc None m (seg_rom bsegs)).
End CANSEC1.
