(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface AllocCover.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition MAX_REQ_D : Z := 2 ^ 27.

(* [comment removed for export] *)
Definition alloc_dcv_law (segs : list Segment) (L : alloc_layout) (AI : AllocIface segs L) (AC : AllocCover segs L AI) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
         (s : ai_AS AI) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> ac_vm AC (ac_cost n + k)%nat s MD ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n -> 0 <= n <= MAX_REQ_D ->
    (forall (s' : ai_AS AI) (LB' : list ablock) (m' : word -> option byte) (MD' : Model) (r : Z)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv AI s' LB' m' MD' -> vm_only MD MD' -> ac_vm AC k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        ((r = 0 /\ LB' = LB)
         \/ (r <> 0 /\ block_ok L r n /\ (exists p, LB' = (p, r, n) :: LB /\ ~ In p (map blk_id LB))
             /\ exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk])) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) T.

(* [comment removed for export] *)
Definition alloc_freev_law (segs : list Segment) (L : alloc_layout) (AI : AllocIface segs L) (AC : AllocCover segs L AI) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
         (s : ai_AS AI) (LB : list ablock) (k : nat) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> ac_vm AC k s MD -> In (p, A, n) LB ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ai_inv AI s' (lb_remove p LB) m' MD' -> vm_only MD MD' -> ac_vm AC k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv] -> ai_aux AI m' B ->
        heap_pres segs L (lb_remove p LB) (bv_unsigned sp) m m' ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free L)) fc None m (seg_rom segs)) MD) T.

End ACeilS1.
