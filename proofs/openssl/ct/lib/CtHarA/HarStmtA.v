(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG CtSizes CtWire CtTime CtModel ApBase ApState ApErr ApParse ApBridge.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs D_libiface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA W_ex_dataA W_ex_dataA2 CtFuzzStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA SctStmtA SctStmtA2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnA Require Import PrnStmtA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BIO_S_NULL_A : Z := 0x3233c0.        (* [comment removed for export] *)
Definition BIO_NEW_A : Z := 0x237894.           (* [comment removed for export] *)
Definition BIO_NEW_EX_A : Z := 0x23769c.
Definition BIO_FREE_A : Z := 0x2378bc.          (* [comment removed for export] *)
Definition BIO_FREE_INT_A : Z := 0x2378e4.
Definition A_FUZZ_CT_C_A : Z := 0x49200.        (* [comment removed for export] *)
Definition HAR_FRAME_A : Z := 128.              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition BIO_NEW_NULL_STACK_A : Z := 16 + 64 + Z.max CRYPTO_ZALLOC_STACK NEW_EX_DATA_STACK_A.
Definition BIO_NEW_NULL_COST_A : Z := 1.
Definition BIO_FREE_NULL_STACK_A : Z := 32 + 48 + Z.max CRYPTO_FREE_STACK FREE_EX_DATA_STACK_A.
Definition BIO_FREE_NULL_COST_A : Z := 1.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation FR := (@ar_FR AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bio_null_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (m : mem) (pb : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' A,
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (wz A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ - BIO_NEW_NULL_COST_A <= rt_credit RT Σ'
    /\ ablock_range A BIO_SIZE /\ AHEAP Σ' ((pb, A, BIO_SIZE) :: OW) LB m'
    /\ rw_cells ctasegs m' A (bio_null_cells NULL_METHOD 0 0)
    /\ exlock_free m' E.

Definition BIO_new_null_specA : Prop :=
  forall (X : Type) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (ras : list Z)
         (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
    AHEAP Σ OW LB m ->
    stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BIO_NEW_NULL_STACK_A ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
    mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> BIO_NEW_NULL_COST_A <= rt_credit RT Σ ->
    ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) OW ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BIO_NEW_A (bv_unsigned ra :: ras) ->
    a0 = wz NULL_METHOD ->
    (forall pb Σ' ms', ~ In pb (map blk_id (OW ++ LB)) ->
       bio_null_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m pb Σ' ms' -> implAp (k (Some pb)) Σ' Q ms') ->
    implAp (AMalloc SZ_BIO k) Σ Q
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz BIO_NEW_A) fc None m (seg_rom ctasegs)).

Definition bio_free_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (E : ap_env) (pb : bptr) (lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (aclient_addr (lb_remove pb OW ++ LB) (bv_unsigned sp)) m m'
    /\ rt_credit RT Σ - BIO_FREE_NULL_COST_A <= rt_credit RT Σ'
    /\ AHEAP Σ' (lb_remove pb OW) LB m'
    /\ exlock_free m' E.

Definition BIO_free_null_specA : Prop :=
  forall (X : Type) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (E : ap_env) (lo : Z) (ras : list Z)
         (pb : bptr) (A nxt prev nw : Z)
         (k : aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop),
    AHEAP Σ OW LB m -> In (pb, A, BIO_SIZE) OW -> pb <> p_xl E ->
    stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo <= bv_unsigned sp - BIO_FREE_NULL_STACK_A ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
    mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> BIO_FREE_NULL_COST_A <= rt_credit RT Σ ->
    ap_statics_fixed m E -> exlock_free m E -> In (p_xl E, e_xl E, MUTEX_SIZE) OW ->
    rw_cells ctasegs m A (bio_cells NULL_METHOD 1 0 nxt prev nw) ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx BIO_FREE_A (bv_unsigned ra :: ras) ->
    a0 = wz A ->
    (forall Σ' ms', bio_free_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E pb lo m Σ' ms' -> implAp k Σ' Q ms') ->
    implAp (AFree pb k) Σ Q
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz BIO_FREE_A) fc None m (seg_rom ctasegs)).

End WithRT.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Decomposition.
  Context {AR : ARun} {UK : UnwindKit}.
  (* [comment removed for export] *)
  Variables (STK_D2I : Z) (CST_D2I : Z -> Z) (FRM_D2I : Z).
  Variables (STK_PRN : Z) (CST_PRN : Z -> Z) (FRM_PRN : Z).
  Variables (STK_I2D : Z) (CST_I2D : Z -> Z) (FRM_I2D : Z).
  Variable  (STK_FREE : Z).

  (* [comment removed for export] *)
  Definition har_budgetsA : Prop :=
    0 <= STK_D2I <= CT_FUZZ_STACK_A - HAR_FRAME_A /\ 0 <= STK_PRN <= CT_FUZZ_STACK_A - HAR_FRAME_A
    /\ 0 <= STK_I2D <= CT_FUZZ_STACK_A - HAR_FRAME_A /\ 0 <= STK_FREE <= CT_FUZZ_STACK_A - HAR_FRAME_A
    /\ 0 <= FRM_D2I <= CT_FUZZ_FRAMES_A - 1 /\ 0 <= FRM_PRN <= CT_FUZZ_FRAMES_A - 1 /\ 0 <= FRM_I2D <= CT_FUZZ_FRAMES_A - 1
    /\ (forall n, 0 <= n < 2^26 -> 0 <= CST_D2I n <= 2^30 + 2^27) /\ (forall n, 0 <= n < 2^26 -> 0 <= CST_PRN n <= 2^28)
    /\ (forall n, 0 <= n < 2^26 -> 0 <= CST_I2D n <= 2^28).

  (* [comment removed for export] *)
  Definition har_hypsA : Prop :=
    (forall f, @d2i_sct_list_specA2 (push AR f 1) UK STK_D2I CST_D2I FRM_D2I)   (* [comment removed for export] *)
    /\ (forall f, @SCT_LIST_print_specA (push AR f 1) UK STK_PRN CST_PRN FRM_PRN)
    /\ (forall f, @i2d_sct_list_specA (push AR f 1) UK STK_I2D CST_I2D FRM_I2D)
    /\ (forall f, @sct_list_free_specA (push AR f 1) UK STK_FREE)
    /\ (forall f, @BIO_new_null_specA (push AR f 1) UK)
    /\ (forall f, @BIO_free_null_specA (push AR f 1) UK)
    /\ (forall f, @ERR_clear_error_specA (push AR f 1) UK).

  (* [comment removed for export] *)
  Definition har_goalA : Prop := har_budgetsA -> har_hypsA -> ct_fuzz_stmtA.
End Decomposition.
