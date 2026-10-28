(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas FuzzProducer.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation APZD_RESERVE := 0xb0290 (only parsing).   (* [comment removed for export] *)
Notation APZD_U32R := 0xb0150 (only parsing).   (* [comment removed for export] *)
Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.


(* [comment removed for export] *)
Definition prod_at (m : amem) (P D size : Z) : Prop :=
  rw_cells bsegs m P [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 size)].
Definition payload_at (m : amem) (D : Z) (pl : list Z) : Prop :=
  bytes_at bsegs m D (map (Z_to_bv 8) pl) /\ Forall (fun c => 0 <= c < 256) pl.

Definition prod_u32r_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (uint32Range pl size mn mx))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(P + 8, P + 16); (SPV - 16, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ prod_at m' P D (snd (uint32Range pl size mn mx)).

(* [comment removed for export] *)
Definition zd_u32r_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D : Z) (pl : list Z) (size mn mx lo : Z),
  prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl ->
  0 < P -> P mod 8 = 0 -> 0 < D ->
  stk bsegs m lo SPV -> lo <= SPV - 16 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  (* [comment removed for export] *)
  areg RNG m P 16 -> aro RNG m D (zlen pl) -> art m -> astk RNG lo SPV -> SPV < 2^47 ->
  mem_inv bsegs m ->
  0 <= mn <= mx -> mx < 2^31 ->
  a0 = Z_to_bv 64 P -> a1 = Z_to_bv 64 mn -> a2 = Z_to_bv 64 mx ->
  evtF bsegs RNG (prod_u32r_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size mn mx lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_U32R) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition zd_reserve_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV P D : Z) (pl : list Z) (size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (reserve_data_prefix pl size))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(P, P + 16); (SPV - 64, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ prod_at m' P (D + fst (reserve_data_prefix pl size)) (snd (reserve_data_prefix pl size)).

Definition zd_reserve_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV P D : Z) (pl : list Z) (size lo : Z),
  prod_at m P D size -> payload_at m D pl -> 0 <= size <= zlen pl -> size < 2^31 ->
  0 < P -> P mod 8 = 0 -> 0 < D -> D + zlen pl < 2^64 ->
  stk bsegs m lo SPV -> lo <= SPV - 64 -> 0 <= SPV < 2^64 ->
  P + 16 <= lo -> D + zlen pl <= lo -> (D + zlen pl <= P \/ P + 16 <= D) ->
  (* [comment removed for export] *)
  areg RNG m P 16 -> aro RNG m D (zlen pl) -> art m -> astk RNG lo SPV -> SPV < 2^47 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 P ->
  evtF bsegs RNG (zd_reserve_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV P D pl size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_RESERVE) fc None m (seg_rom bsegs)).
End CANSEC1.
