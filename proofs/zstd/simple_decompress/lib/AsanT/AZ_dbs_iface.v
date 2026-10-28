(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit AZ_seq_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition APZD_DBS : Z := 0x96540.   (* [comment removed for export] *)
Notation DBS_STACK_A := 2304 (only parsing).   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Definition zd_dbs_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV OP LEN B0 B1 R0 R1 lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(OP, OP + LEN); (SPV - DBS_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV /\ stk bsegs m' B0 B1 /\ rdbl bsegs m' R0 R1.

Definition zd_dbs_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo OP IP LEN B0 B1 R0 R1 : Z),
  stk bsegs m B0 B1 -> 4096 <= B0 -> B1 < 2^47 -> B0 <= OP -> 0 <= LEN -> OP + LEN <= B1 ->
  rdbl bsegs m R0 R1 -> 4096 <= R0 -> R1 < 2^47 -> R0 <= IP -> IP + LEN <= R1 ->
  (apart R0 (R1 - R0) B0 (B1 - B0) \/ (B0 <= R0 /\ R1 <= B1)) ->
  stk bsegs m lo SPV -> lo <= SPV - DBS_STACK_A -> 0 <= SPV < 2^47 ->
  off_stack lo SPV B0 (B1 - B0) -> off_stack lo SPV R0 (R1 - R0) ->
  (* [comment removed for export] *)
  B0 < B1 -> areg RNG m B0 (B1 - B0) -> ahull RNG m B0 (B1 - B0) ->
  areg RNG m R0 (R1 - R0) -> ahull RNG m R0 (R1 - R0) -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 OP -> a1 = Z_to_bv 64 IP -> a2 = Z_to_bv 64 LEN ->
  evtF bsegs RNG (zd_dbs_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV OP LEN B0 B1 R0 R1 lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_DBS) fc None m (seg_rom bsegs)).
End CANSEC1.
