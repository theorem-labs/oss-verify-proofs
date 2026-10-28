(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Image ZBridge SysStep ITree Nodes Decode Arr FP Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed Harness ProgA AsanProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount ZdFrame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AProg_kit AZ_kit AZ_frame_iface AZ_dframe_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".

Section CANSEC1. Context {rc : runConstT}.
Definition ACREATEDCTX_MRET : Z := 0x82cd8.   (* [comment removed for export] *)
Definition AFREEDCTX_FRET : Z := 0x831b8.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CREATEDCTX_STACK_A : Z := 64 + AMALLOC_STACK.
Definition FREEDCTX_STACK_A : Z := 64 + AFREE_STACK.

Section Stmts.
  Variable AI : AMallocIface.
  Notation CI := (aci AI).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition zd_createdctx_postA (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (lo : Z) (m : amem)
      (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (p : AsanCtrl.aptr) (A : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ r = Some p
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI LB (bv_unsigned sp) m m'
      /\ aps_rest s' = aps_rest s
      /\ ablock_range A DCTX_SIZE
      /\ AHEAP AI L RNG' (aps_m s') (HB p A DCTX_SIZE :: LB) m'
      /\ dctx_any m' A
      /\ rng RNG' A DCTX_SIZE /\ rng RNG' (shad A) (shlen (DCTX_SIZE + 7)).

  Definition zd_createdctx_stmtA : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (lo : Z),
    AHEAP AI L RNG (aps_m s) LB m ->
    mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - CREATEDCTX_STACK_A ->
    bv_unsigned sp < al_top L -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 ATP ->
    bv_unsigned s0 < ATOP ->                                   (* [comment removed for export] *)
    In [AMALLOC_PC; ACREATEDCTX_MRET] (al_U L) ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
    aps_ok L s ->
    implMA RNG (amalloc_M DCTX_SIZE) s
           (zd_createdctx_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 APZD_CREATEDCTX) fc None m (seg_rom bsegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition zd_freedctx_postA (L : alayout) (RNG : footprint)
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
      (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (lo : Z) (m : amem)
      (r : unit) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
    fun ms' => fp_le RNG RNG' /\ exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ aheap_pres CI (lb_remove p LB) (bv_unsigned sp) m m'
      /\ aps_rest s' = aps_rest s
      /\ AHEAP AI L RNG' (aps_m s') (lb_remove p LB) m'.

  Definition zd_freedctx_stmtA : Prop :=
    forall (L : alayout) (RNG : footprint)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (FR : bvmap 5 word) (fc : bv 32) (m : amem)
           (s : APS) (LB : list ablock) (p : AsanCtrl.aptr) (A lo : Z),
    AHEAP AI L RNG (aps_m s) LB m -> In (HB p A DCTX_SIZE) LB -> dctx_any m A ->
    mem_inv bsegs m ->
    stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - FREEDCTX_STACK_A ->
    bv_unsigned sp + 16 < al_top L -> bv_unsigned sp mod 16 = 0 ->
    tp = Z_to_bv 64 ATP ->
    a0 = Z_to_bv 64 A ->
    In [AFREE_PC; AFREEDCTX_FRET] (al_U L) ->
    rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
    aps_ok L s ->
    implMA RNG (afree_M p) s
           (zd_freedctx_postA L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB p lo m)
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               FR (Z_to_bv 64 APZD_FREEDCTX) fc None m (seg_rom bsegs)).
End Stmts.
End CANSEC1.
