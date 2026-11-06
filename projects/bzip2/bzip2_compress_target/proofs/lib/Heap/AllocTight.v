(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Section ACeilS1. Context {ACEIL__ : ACeil}.


Definition MMAP_THRESHOLD_Z : Z := 131052.   (* [comment removed for export] *)
Definition MAX_REQ : Z := 2^26.              (* [comment removed for export] *)

Record AllocTight (segs : list Segment) (L : alloc_layout) (AI : AllocIface segs L) : Type := mkAllocTight {
  at_tight : ai_AS AI -> list ablock -> Model -> Prop;

  (* [comment removed for export] *)
  at_sys : forall s LB m MD n, ai_inv AI s LB m MD -> at_tight s LB MD -> 0 < n <= MAX_REQ -> ai_sys_ok AI s LB n MD;

  (* [comment removed for export] *)
  at_model_frame : forall s LB MD MD', at_tight s LB MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> at_tight s LB MD';

  (* [comment removed for export] *)
  at_mat : forall s LB MD, at_tight s LB MD -> m_vm_materialized MD = [];

  (* [comment removed for export] *)
  at_malloc_big : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (n lo B : Z) (errv : word) (Tok : TSet),
    ai_inv AI s LB m MD -> at_tight s LB MD -> length LB = 1%nat -> MMAP_THRESHOLD_Z <= n <= MAX_REQ ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv AI s' ((p, r, n) :: LB) m' MD' -> at_tight s' ((p, r, n) :: LB) MD' -> vm_only MD MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r n -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat n) junk] ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') Tok) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) Tok;

  (* [comment removed for export] *)
  at_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> at_tight s LB MD -> length LB = 2%nat -> In (p, A, n) LB ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ai_inv AI s' (lb_remove p LB) m' MD' -> at_tight s' (lb_remove p LB) MD' -> vm_only MD MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv] -> ai_aux AI m' B ->
        heap_pres segs L (lb_remove p LB) (bv_unsigned sp) m m' ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free L)) fc None m (seg_rom segs)) MD) T
}.
End ACeilS1.


Arguments at_tight {ACEIL__ segs L AI} _ _ _ _.
Arguments at_sys {ACEIL__ segs L AI} _ [s LB m MD n] _ _ _.
Arguments at_model_frame {ACEIL__ segs L AI} _ [s LB MD MD'] _ _ _.
Arguments at_mat {ACEIL__ segs L AI} _ [s LB MD] _.
Arguments at_malloc_big {ACEIL__ segs L AI} _.
Arguments at_free {ACEIL__ segs L AI} _.
