(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
Import ListNotations.
Open Scope Z_scope.

Notation PZD_RESERVE := 0x2d7dc (only parsing).
Notation PZD_U32R := 0x2d6c4 (only parsing).
Notation fmem := (word -> option byte).
Notation zlen l := (Z.of_nat (length l)).

(* [comment removed for export] *)
Definition prod_at (m : fmem) (P D size : Z) : Prop :=
  rw_cells usegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)].
Definition payload_at (m : fmem) (D : Z) (pl : list Z) : Prop :=
  bytes_at usegs m D (map (Z_to_bv 8) pl) /\ Forall (fun c => 0 <= c < 256) pl.

Definition prod_u32r_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (uint32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(P + 8, P + 16); (SPV - 16, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ prod_at m' P D (snd (uint32Range pl size mn mx)).

(* [comment removed for export] *)
Definition zd_u32r_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
  prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl ->
  0 < P -> P mod 8 = 0 -> 0 < D ->
  stk usegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  mem_inv usegs m ->
  0 <= mn <= mx -> mx < 2^31 ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
  evt usegs (prod_u32r_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_U32R) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition zd_reserve_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV P D : Z) (pl : list Z) (size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (reserve_data_prefix pl size))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(P, P + 16); (SPV - 32, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ prod_at m' P (D + fst (reserve_data_prefix pl size)) (snd (reserve_data_prefix pl size)).

Definition zd_reserve_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV P D : Z) (pl : list Z) (size lo : Z),
  prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl -> size < 2^31 ->
  0 < P -> P mod 8 = 0 -> 0 < D -> D + zlen pl < 2^64 ->
  stk usegs m lo SPV -> lo <= SPV - 32 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 P ->
  evt usegs (zd_reserve_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_RESERVE) fc None m (seg_rom usegs)).
