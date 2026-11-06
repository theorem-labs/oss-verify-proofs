(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs CJ_iface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition DRV_CALLS : nat := 32%nat.
(* [comment removed for export] *)
Definition DRV_REQ_MAX : Z := 2^26.
(* [comment removed for export] *)
Definition DRV_BFLOOR : Z := 2^39 - 2^35 + 2^27.

Section CeilWrap.
Context {ACEIL : Ceil}.

Section Stmts.
  Variable ART : Z -> Z -> list cblock -> list fframe -> list (list Z) -> Z -> (word -> option byte) -> Model -> lghost -> Prop.
  Variable ADRV : nat -> (word -> option byte) -> Model -> lghost -> Prop.

  (* [comment removed for export] *)
  Definition amalloc_nn_post (k : nat) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z) (tr : list Z)
      (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
    fun ms' mo' g' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : word -> option byte)
                             (errv' : word) (TRS' : list (list Z)) (A : Z) (junk : list byte),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
      /\ rw_cells bsegs m' AERRNO [C4 errv']
      /\ cj_pres sp0 LB LF (bv_unsigned sp) m m'
      /\ gmono g g' /\ trs_put tr TRS TRS'
      /\ A <> 0 /\ ablock_range A n /\ ~ In A (map fst LB)
      /\ (forall Fr kk, In (Fr, kk) LF -> A + n <= Fr \/ Fr + fsz kk <= A)
      /\ ART sp0 SPB ((A, n) :: LB) LF TRS' (B - cost_malloc n) m' mo' g'
      /\ ADRV k m' mo' g'
      /\ rw_cells bsegs m' A [CB (Z.to_nat n) junk].

  (* [comment removed for export] *)
  Definition malloc_nn_stmt : Prop :=
    forall (k : nat)
           (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
           (sp0 SPB : Z) (LB : list cblock) (LF : list fframe) (TRS : list (list Z)) (B : Z)
           (n lo : Z) (errv : word) (tl : list Z),
    ART sp0 SPB LB LF TRS B m mo g -> ADRV (S k) m mo g ->
    bv_unsigned sp <= SPB ->
    stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
    rw_cells bsegs m AERRNO [C4 errv] ->
    mem_inv bsegs m ->
    tp = wz ATP ->
    a0 = wz n -> 0 < n <= DRV_REQ_MAX ->
    cost_malloc n <= B -> DRV_BFLOOR <= B ->
    (is_primary n = true -> k = 0%nat) ->          (* [comment removed for export] *)
    4096 <= bv_unsigned ra /\ bv_unsigned ra <> PC0_MALLOC ->
    uwt m (bv_unsigned sp) (ASTACK_TOP sp0) PC0_MALLOC (bv_unsigned sp) (bv_unsigned s0) 2 tl ->
    trs_room (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) TRS ->
    LSCPS bsegs (amalloc_nn_post k ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc sp0 SPB LB LF TRS B
                                 (hook_tr PC0_MALLOC sp0 (bv_unsigned sp) (bv_unsigned ra) tl) n lo m g)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (wz AMALLOC) fc None m (seg_rom bsegs)) mo g.
End Stmts.

(* [comment removed for export] *)
Record drv_iface2 (AI : art_iface) := mkDI2 {
  ADRV : nat -> (word -> option byte) -> Model -> lghost -> Prop;
  (* [comment removed for export] *)
  adrv_weaken : forall k k' m mo g, ADRV k m mo g -> (k' <= k)%nat -> ADRV k' m mo g;
  adrv_frame : forall k sp0 SPB LB LF TRS B m m' mo g W,
      CJ_iface.ART AI sp0 SPB LB LF TRS B m mo g -> ADRV k m mo g -> munch W m m' -> wmono bsegs m m' ->
      Forall (cj_write_ok sp0 SPB LB LF) W -> ADRV k m' mo g;
  adrv_model : forall k m mo mo' g, ADRV k m mo g ->
      m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None -> ADRV k m mo' g;
  (* [comment removed for export] *)
  art2_free : forall k, free_lscps_stmt
      (fun sp0 SPB LB LF TRS B m mo g => CJ_iface.ART AI sp0 SPB LB LF TRS B m mo g /\ ADRV k m mo g);
  (* [comment removed for export] *)
  art2_malloc : malloc_nn_stmt (CJ_iface.ART AI) ADRV
}.
(* [comment removed for export] *)
End CeilWrap.
