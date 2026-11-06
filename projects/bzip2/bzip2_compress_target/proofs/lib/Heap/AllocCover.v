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


Definition FILE_SZ : Z := 1264.                (* [comment removed for export] *)
Definition MMAP_THRESHOLD_C : Z := 131052.
Definition MAX_REQ_C : Z := 2^26.

(* [comment removed for export] *)
Definition ac_cost (n : Z) : nat := if n <? 1024 then 4%nat else 1%nat.

(* [comment removed for export] *)
Definition t_incl (A B : TSet) : Prop := forall tr, A tr -> B tr.

(* [comment removed for export] *)
Definition c21_foreign (n : Z) : Prop :=
  n = 36 \/ n = 5104 \/ n = 55768 \/ n = 64144 \/ (MMAP_THRESHOLD_C <= n <= MAX_REQ_C).

(* [comment removed for export] *)
Inductive c21_occ : Type :=
  | C21_none                      (* [comment removed for export] *)
  | C21_idle                      (* [comment removed for export] *)
  | C21_one (f1 : bid)            (* [comment removed for export] *)
  | C21_two (f1 f2 : bid).        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition c21_after_free (o : c21_occ) (p : bid) (n : Z) : c21_occ :=
  match o with
  | C21_none => C21_none
  | C21_idle => C21_idle
  | C21_one f1 => if bid_eqb p f1 then C21_idle else o
  | C21_two f1 f2 => if bid_eqb p f1 then C21_one f2 else if bid_eqb p f2 then C21_one f1 else o
  end.

Record AllocCover (segs : list Segment) (L : alloc_layout) (AI : AllocIface segs L) : Type := mkAllocCover {
  (* [comment removed for export] *)
  ac_can : Z -> ai_AS AI -> list ablock -> Model -> Prop;
  (* [comment removed for export] *)
  ac_vm : nat -> ai_AS AI -> Model -> Prop;
  ac_vm_frame : forall k s MD MD', ac_vm k s MD -> m_vm MD' = m_vm MD -> m_halted MD' = None -> ac_vm k s MD';
  ac_vm_le : forall k k' s MD, ac_vm k s MD -> (k' <= k)%nat -> ac_vm k' s MD;
  (* [comment removed for export] *)
  ac_c21 : c21_occ -> ai_AS AI -> list ablock -> Prop;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ac_malloc_cover : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (Tf To : TSet),
    ai_inv AI s LB m MD -> ac_vm (ac_cost n + k) s MD -> ac_can n s LB MD ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n -> 0 <= n < MMAP_THRESHOLD_C ->
    (* [comment removed for export] *)
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv AI s' LB m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        (forall o, ac_c21 o s LB -> n <> FILE_SZ -> ac_c21 o s' LB) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') Tf) ->
    (* [comment removed for export] *)
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv AI s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r n -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat n) junk] ->
        (forall o, ac_c21 o s LB -> c21_foreign n -> ac_c21 o s' ((p, r, n) :: LB)) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') To) ->
    t_incl Tf To ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) To;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ac_malloc_big : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> ac_vm (S k) s MD -> ac_can n s LB MD -> MMAP_THRESHOLD_C <= n <= MAX_REQ_C ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv AI s' LB m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        (forall o, ac_c21 o s LB -> ac_c21 o s' LB) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv AI s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r n -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat n) junk] ->
        (forall o, ac_c21 o s LB -> ac_c21 o s' ((p, r, n) :: LB)) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) T;

  (* [comment removed for export] *)
  ac_malloc_bigz : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> ac_vm (S k) s MD -> ac_can n s LB MD -> MMAP_THRESHOLD_C <= n <= MAX_REQ_C ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv AI s' LB m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        (forall o, ac_c21 o s LB -> ac_c21 o s' LB) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv AI s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r n -> ~ In p (map blk_id LB) ->
        rw_cells segs m' r [CB (Z.to_nat n) (repeat (Z_to_bv 8 0) (Z.to_nat n))] ->
        (forall o, ac_c21 o s LB -> ac_c21 o s' ((p, r, n) :: LB)) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ac_malloc_sys : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (n lo B : Z) (errv : word) (Tok : TSet),
    ai_inv AI s LB m MD -> ai_sys_ok AI s LB n MD -> ac_vm (ac_cost n + k) s MD -> ac_c21 C21_none s LB ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] -> mem_inv segs m -> tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 n -> 0 < n <= MAX_REQ_C ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv AI s' ((p, r, n) :: LB) m' MD' -> vm_only MD MD' -> ac_vm k s' MD' -> ac_c21 C21_idle s' ((p, r, n) :: LB) ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r n -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat n) junk] ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') Tok) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) Tok;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ac_malloc_fast : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (f1 : bid) (lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> ac_c21 (C21_one f1) s LB -> ac_vm k s MD ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 FILE_SZ ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv AI s' ((p, r, FILE_SZ) :: LB) m' MD -> ac_vm k s' MD ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r FILE_SZ -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat FILE_SZ) junk] ->
        ac_c21 (C21_two f1 p) s' ((p, r, FILE_SZ) :: LB) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD) T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ac_can_intro : forall n k s LB m MD, ai_inv AI s LB m MD -> ac_vm (ac_cost n + k) s MD ->
      (c21_foreign n \/ (n = FILE_SZ /\ ac_c21 C21_idle s LB)) -> ac_can n s LB MD;
  (* [comment removed for export] *)
  ac_malloc_first : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (lo B : Z) (errv : word) (Tf To : TSet),
    ai_inv AI s LB m MD -> ac_c21 C21_idle s LB -> ac_vm (S k) s MD ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 FILE_SZ ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word),
        ai_inv AI s' LB m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' -> ac_c21 C21_idle s' LB ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') Tf) ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model) (r : Z) (p : bid)
            (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' errv' : word) (junk : list byte),
        ai_inv AI s' ((p, r, FILE_SZ) :: LB) m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv'] -> ai_aux AI m' B ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        r <> 0 -> block_ok L r FILE_SZ -> ~ In p (map blk_id LB) -> rw_cells segs m' r [CB (Z.to_nat FILE_SZ) junk] ->
        ac_c21 (C21_one p) s' ((p, r, FILE_SZ) :: LB) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') To) ->
    t_incl Tf To ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_malloc L)) fc None m (seg_rom segs)) MD) To;
  (* [comment removed for export] *)
  ac_free : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
      (s : ai_AS AI) (LB : list ablock) (k : nat) (p : bid) (A n lo B : Z) (errv : word) (T : TSet),
    ai_inv AI s LB m MD -> ac_vm k s MD -> In (p, A, n) LB -> (c21_foreign n \/ n = FILE_SZ) ->
    ai_aux AI m B -> bv_unsigned sp <= B ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - al_stack L ->
    rw_cells segs m (errno_cell L) [C4 errv] ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (al_tp L) ->
    a0 = Z_to_bv 64 A ->
    (forall (s' : ai_AS AI) (m' : word -> option byte) (MD' : Model)
            (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ai_inv AI s' (lb_remove p LB) m' MD' -> vm_only MD MD' -> ac_vm k s' MD' ->
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> rw_cells segs m' (errno_cell L) [C4 errv] -> ai_aux AI m' B ->
        heap_pres segs L (lb_remove p LB) (bv_unsigned sp) m m' ->
        (forall o, ac_c21 o s LB -> ac_c21 (c21_after_free o p n) s' (lb_remove p LB)) ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                  F (ret_pc ra) fc None m' (seg_rom segs)) MD') T) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 (al_free L)) fc None m (seg_rom segs)) MD) T;
  (* [comment removed for export] *)
  ac_c21_perm : forall o s LB LB', Permutation.Permutation LB LB' -> ac_c21 o s LB -> ac_c21 o s LB';
  ac_c21_none_idle : forall s LB, ac_c21 C21_none s LB -> ac_c21 C21_idle s LB
}.
End ACeilS1.


Arguments ac_can {ACEIL__ segs L AI} _.
Arguments ac_vm {ACEIL__ segs L AI} _.
Arguments ac_c21 {ACEIL__ segs L AI} _.
Arguments ac_malloc_cover {ACEIL__ segs L AI} _.
Arguments ac_malloc_big {ACEIL__ segs L AI} _.
Arguments ac_malloc_bigz {ACEIL__ segs L AI} _.
Arguments ac_malloc_sys {ACEIL__ segs L AI} _.
Arguments ac_malloc_fast {ACEIL__ segs L AI} _.
Arguments ac_malloc_first {ACEIL__ segs L AI} _.
Arguments ac_can_intro {ACEIL__ segs L AI} _.
Arguments ac_free {ACEIL__ segs L AI} _.

(* [comment removed for export] *)
