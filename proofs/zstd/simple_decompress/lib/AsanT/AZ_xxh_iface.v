(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit AZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition zd_xxh_update_stmtA2 : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV STA IN : Z) (inb : list byte) (msz lo : Z),
  xxh_state m STA msz -> 0 <= msz < 32 -> 4096 <= STA -> STA mod 8 = 0 -> STA + 88 <= 2^47 ->
  ((IN = 0 /\ a2 = Z_to_bv 64 0)
   \/ (bytes_at bsegs m IN inb /\ a2 = Z_to_bv 64 (zlen inb) /\ 4096 <= IN /\ IN + zlen inb <= 2^47 /\
       (STA + 88 <= IN \/ IN + zlen inb <= STA) /\ (IN + zlen inb <= lo \/ SPV <= IN) /\
       aregU RNG m IN (zlen inb) /\ ahull RNG m IN (zlen inb))) ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - XXH_UPDATE_STACK_A -> SPV < 2^47 ->
  (STA + 88 <= lo \/ SPV <= STA) ->
  (* [comment removed for export] *)
  areg RNG m STA 88 -> ahull RNG m STA 88 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 STA -> a1 = Z_to_bv 64 IN ->
  evtF bsegs RNG (zd_xxh_update_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV STA lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_XXH_UPDATE) fc None m (seg_rom bsegs)).
End CANSEC1.
