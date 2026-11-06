(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac AEvt Shape HeapIface.
Import ListNotations.
Open Scope Z_scope.

Section Stmts.
Variable segs : list Segment.
Variable L : heap_layout.
Variable HI : heap_iface segs L.
Variable DRV : nat -> HST segs L HI -> Model -> Prop.
Variable nosmall : HST segs L HI -> Prop.

Definition MMAP_THRESHOLD_Z : Z := 131052.

(* [comment removed for export] *)
Definition malloc_rz_stmt : Prop :=
  forall (k : nat)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST segs L HI) (LB : list blk) (n lo : Z)
         (A B : TSet),
    HEAP segs L HI h LB m mo -> DRV (S k) h mo ->
    stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
    mem_inv segs m ->
    tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned sp <= heap_top segs L HI h ->
    a0 = Z_to_bv 64 n -> 0 <= n <= 2 ^ 26 ->
    A [] -> B [] ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (h' : HST segs L HI),
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> mo_frame mo mo' ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        heap_top segs L HI h' = heap_top segs L HI h ->
        HEAP segs L HI h' LB m' mo' -> MOK mo' ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom segs)) mo') A) ->
    (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (mo' : Model) (h' : HST segs L HI)
            (A0 : Z) (junk : list byte),
        mem_inv segs m' -> stk segs m' lo (bv_unsigned sp) -> mo_frame mo mo' ->
        heap_pres segs L LB (bv_unsigned sp) m m' ->
        heap_top segs L HI h' = heap_top segs L HI h ->
        block_range L A0 n -> HEAP segs L HI h' ((A0, n) :: LB) m' mo' -> MOK mo' ->
        rw_cells segs m' A0 [CB (Z.to_nat n) junk] ->
        (((n = 65536 /\ nosmall h) \/ MMAP_THRESHOLD_Z <= n) -> DRV k h' mo') ->
        realizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 A0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom segs)) mo') B) ->
    realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs)) mo) (t_alt2 A B).

(* [comment removed for export] *)
Definition free_c_stmt : Prop :=
  forall (k : nat)
      (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (h : HST segs L HI) (LB : list blk) (A n lo : Z),
      HEAP segs L HI h LB m mo -> DRV k h mo -> In (A, n) LB ->
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack L ->
      mem_inv segs m ->
      tp = Z_to_bv 64 (hl_tp L) -> bv_unsigned sp <= heap_top segs L HI h ->
      a0 = Z_to_bv 64 A ->
      aevt segs
        (call_post segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (fun _ m' mo' =>
            mem_inv segs m' /\ stk segs m' lo (bv_unsigned sp) /\ mo_frame mo mo'
            /\ heap_pres segs L (lb_remove A LB) (bv_unsigned sp) m m'
            /\ exists h', heap_top segs L HI h' = heap_top segs L HI h /\ HEAP segs L HI h' (lb_remove A LB) m' mo'
                          /\ DRV k h' mo'))
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (hl_free L)) fc None m (seg_rom segs)) mo).

(* [comment removed for export] *)
Definition drv_mo_stmt : Prop :=
  forall k h mo mo', DRV k h mo ->
    m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_vm_materialized mo' = m_vm_materialized mo ->
    m_halted mo' = m_halted mo -> DRV k h mo'.

(* [comment removed for export] *)
Definition drv_le_stmt : Prop := forall k k' h mo, DRV k h mo -> (k' <= k)%nat -> DRV k' h mo.

End Stmts.
