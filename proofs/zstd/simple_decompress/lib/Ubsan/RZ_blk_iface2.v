(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdDCtx ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface.
Import ListNotations.
Open Scope Z_scope.

Definition PZD_BUILDSEQ : Z := 0x175b8.        (* [comment removed for export] *)
Notation BUILDSEQ_STACK := 448 (only parsing).   (* [comment removed for export] *)

Definition zd_buildseq_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DTS DTP W DFLT : Z) (k : seq_kind) (ty srcSize : Z) (frw oldp : word) (dt0 : list byte) (wlen : nat) (lo : Z) (m : fmem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r dt' wb' pv,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DTS, DTS + Z.of_nat (length dt0)); (DTP, DTP + 8); (W, W + Z.of_nat wlen); (SPV - BUILDSEQ_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ u8arr usegs m' DTS dt' /\ length dt' = length dt0
    /\ u8arr usegs m' W wb' /\ length wb' = wlen
    /\ rw_cells usegs m' DTP [C8 pv]
    /\ 0 <= r < 2^64
    /\ (zd_is_error r = true
        \/ (r <= srcSize /\
            ((ty = 0 /\ pv = Z_to_bv 64 DFLT /\ dt' = dt0)
             \/ (ty = 3 /\ frw <> Z_to_bv 64 0 /\ pv = oldp /\ dt' = dt0)
             \/ ((ty = 1 \/ ty = 2) /\ pv = Z_to_bv 64 DTS /\
                 exists t, seq_table_ok k t /\
                   firstn (length (seq_table_bytes t)) dt' = map (Z_to_bv 8) (seq_table_bytes t))))).

Definition zd_buildseq_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DTS DTP SRC W DFLT BASE BITS ty : Z) (k : seq_kind)
         (dt0 wb0 : list byte) (srcb : list Z) (oldp nbw : word),
  (* [comment removed for export] *)
  u8arr usegs m DTS dt0 -> Z.of_nat (length dt0) = 8 + 8 * 2^(kind_maxLog k) ->
  rw_cells usegs m DTP [C8 oldp] ->
  u8arr usegs m W wb0 -> 626 <= Z.of_nat (length wb0) ->
  (* [comment removed for export] *)
  bytes_at usegs m SRC (map (Z_to_bv 8) srcb) -> Forall (fun c => 0 <= c < 256) srcb -> Z.of_nat (length srcb) <= 1048576 ->
  bytes_at usegs m BASE (u32s (map (Z_to_bv 64) (kind_base k))) ->
  bytes_at usegs m BITS (map (Z_to_bv 8) (kind_bits k)) ->
  rw_cells usegs m SPV [C8 nbw; C8 (Z_to_bv 64 W)] ->
  0 <= ty <= 3 ->
  (* [comment removed for export] *)
  4096 <= DTS -> DTS + Z.of_nat (length dt0) < 2^47 -> 4096 <= DTP -> DTP + 8 < 2^47 -> 4096 <= W -> W + Z.of_nat (length wb0) < 2^47 ->
  4096 <= SRC -> SRC + Z.of_nat (length srcb) < 2^47 -> 4096 <= BASE < 2^47 -> 4096 <= BITS < 2^47 ->
  stk usegs m lo SPV -> lo <= SPV - BUILDSEQ_STACK -> 4096 <= lo -> SPV + 16 < 2^47 ->
  off_stack lo SPV DTS (Z.of_nat (length dt0)) -> off_stack lo SPV DTP 8 -> off_stack lo SPV W (Z.of_nat (length wb0)) ->
  off_stack lo SPV SRC (Z.of_nat (length srcb)) -> off_stack lo SPV BASE 212 -> off_stack lo SPV BITS 53 ->
  apart DTS (Z.of_nat (length dt0)) DTP 8 -> apart DTS (Z.of_nat (length dt0)) W (Z.of_nat (length wb0)) ->
  apart DTS (Z.of_nat (length dt0)) SRC (Z.of_nat (length srcb)) -> apart DTS (Z.of_nat (length dt0)) BASE 212 ->
  apart DTS (Z.of_nat (length dt0)) BITS 53 -> apart DTS (Z.of_nat (length dt0)) SPV 16 ->
  apart DTP 8 W (Z.of_nat (length wb0)) -> apart DTP 8 SRC (Z.of_nat (length srcb)) -> apart DTP 8 BASE 212 -> apart DTP 8 BITS 53 ->
  apart DTP 8 SPV 16 ->
  apart W (Z.of_nat (length wb0)) SRC (Z.of_nat (length srcb)) -> apart W (Z.of_nat (length wb0)) BASE 212 ->
  apart W (Z.of_nat (length wb0)) BITS 53 -> apart W (Z.of_nat (length wb0)) SPV 16 ->
  DTS mod 4 = 0 -> DTP mod 8 = 0 -> BASE mod 4 = 0 -> W mod 2 = 0 -> SPV mod 16 = 0 -> (t5 <> Z_to_bv 64 0 -> 4096 <= bv_unsigned oldp < 2^47) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DTS -> a1 = Z_to_bv 64 DTP -> a2 = Z_to_bv 64 ty -> a3 = Z_to_bv 64 (kind_max k) -> a4 = Z_to_bv 64 (kind_maxLog k) ->
  a5 = Z_to_bv 64 SRC -> a6 = Z_to_bv 64 (Z.of_nat (length srcb)) -> a7 = Z_to_bv 64 BASE -> t3 = Z_to_bv 64 BITS -> t4 = Z_to_bv 64 DFLT ->
  evt usegs (zd_buildseq_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DTS DTP W DFLT k ty (Z.of_nat (length srcb)) t5 oldp dt0
                              (length wb0) lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_BUILDSEQ) fc None m (seg_rom usegs)).
