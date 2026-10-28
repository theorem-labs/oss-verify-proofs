(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_huf_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Notation zlen l := (Z.of_nat (length l)).

Section CANSEC1. Context {rc : runConstT}.
Definition fast_args_post3A (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV ARGS DST dsz SRC n DT lo : Z) (m : amem) (dth : list byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(ARGS, ARGS + 152); (SPV - FASTARGS_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ((r = 1 /\ exists l1 l2 l3 b0 b1 b2 b3,
           8 <= l1 /\ 8 <= l2 /\ 8 <= l3 /\ 6 + l1 + l2 + l3 + 8 <= n /\ DST + 3 * ((dsz + 3) / 4) < DST + dsz /\
           rw_cells bsegs m' ARGS (fast_args_cells DST dsz SRC n DT l1 l2 l3 b0 b1 b2 b3) /\
           nth_error dth 2 = Some (Z_to_bv 8 11) /\
           bv_unsigned b0 mod 512 <> 0 /\ bv_unsigned b1 mod 512 <> 0 /\ bv_unsigned b2 mod 512 <> 0 /\ bv_unsigned b3 mod 512 <> 0)
        \/ ((r = 0 \/ zd_is_error r = true) /\ 0 <= r < 2^64 /\ exists bs, rw_cells bsegs m' ARGS [CB 152 bs])).

Definition fast_args_stmt3A : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV ARGS DST dsz SRC n DT lo : Z) (src dth junk : list byte),
  mem_inv bsegs m ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - FASTARGS_STACK_A -> SPV < 2^47 ->
  rw_cells bsegs m ARGS [CB 152 junk] -> ARGS mod 8 = 0 -> DT mod 4 = 0 ->      (* [comment removed for export] *)
  bytes_at bsegs m SRC src -> zlen src = n ->
  bytes_at bsegs m DT dth -> zlen dth = 4 ->
  4096 <= ARGS -> ARGS + 152 < 2^47 -> (ARGS + 152 <= lo \/ SPV <= ARGS) ->
  4096 <= SRC -> SRC + n < 2^47 -> (SRC + n <= lo \/ SPV <= SRC) -> n < 2^32 ->
  4096 <= DT -> DT + 4 < 2^47 -> (DT + 4 <= lo \/ SPV <= DT) -> 4096 <= DST -> 0 <= dsz < 2^32 -> DST + dsz < 2^47 ->
  (ARGS + 152 <= SRC \/ SRC + n <= ARGS) -> (ARGS + 152 <= DT \/ DT + 4 <= ARGS) ->
  (* [comment removed for export] *)
  app_blk ARGS (ARGS + 152) -> aro RNG m ARGS 152 -> aro RNG m SRC n -> aro RNG m DT 4 -> art m -> astk RNG lo SPV ->
  evtF bsegs RNG (fast_args_post3A ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV ARGS DST dsz SRC n DT lo m dth)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 ARGS) (Z_to_bv 64 DST) (Z_to_bv 64 dsz) (Z_to_bv 64 SRC)
               (Z_to_bv 64 n) (Z_to_bv 64 DT) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APHUF_FASTARGS) fc None m (seg_rom bsegs)).
End CANSEC1.
