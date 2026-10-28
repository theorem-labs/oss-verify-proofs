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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA BnIfaceA UnwindA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require ApIface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApRepDefs ApRep ApIface W_get_objectA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require Import SctDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctP Require W_sct_list_free SctRep W_sk_leaves SctStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctA Require Import SctWire.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCT_LIST_PRINT_A : Z := 0x338364.
Definition SCT_PRINT_A : Z := 0x337ce8.
Definition A_SEP_A : Z := 0x491e0.        (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun} {UK : UnwindKit}.
Local Notation RT := (@ar_RT AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition sct_print_resA (st : ap_st bptr) (OW : list block) (out pv : Z) : unit * ap_st bptr -> list block -> mem -> word -> Z * Z -> Prop :=
  fun r OW' m' _ _ => r = (tt, st) /\ OW' = OW /\ exists nw', 0 <= nw' < 2^64 /\ rw_cells ctasegs m' out (bio_null_cells NULL_METHOD pv nw').

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCT_print_specA (STK CST FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (x : sctr bptr) (pbio : bptr) (out pv nw : Z),
    ap_preA Σ st m OW LB E bo sp lo STK CST FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_PRINT_A (bv_unsigned ra :: ras) -> ras <> nil ->
    a0 = wz (adr (sc_blk x)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz 0 ->
    sct_repA m (OW ++ LB) adr x -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    In (pbio, out, BIO_SIZE) OW -> ~ In pbio (es_ids st ++ env_ids E) -> ~ In pbio (map blk_id (sct_blocks adr x)) ->
    rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) -> (forall b, In b K -> blk_id b <> pbio) ->
    implAp (sct_print x st) Σ
           (ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K CST (sct_print_resA st OW out pv))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz SCT_PRINT_A) fc None m (seg_rom ctasegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition SCT_LIST_print_specA (STK : Z) (CST : Z -> Z) (FRM : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z)
         (lo : Z) (K : list block) (ras : list Z)
         (adr : bptr -> Z) (k : skr bptr) (pbio : bptr) (out pv nw W : Z),
    ap_preA Σ st m OW LB E bo sp lo STK (CST (zlength (sk_items k))) FRM -> tp = wz TP_A ->
    uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx SCT_LIST_PRINT_A (bv_unsigned ra :: ras) -> ras <> nil ->
    a0 = wz (adr (sk_blk k)) -> a1 = wz out -> a2 = wz 4 -> a3 = wz A_SEP_A -> a4 = wz 0 ->
    sk_repA m LB adr k -> (forall b, In b LB -> adr (blk_id b) = blk_addr b) ->
    In (pbio, out, BIO_SIZE) OW -> ~ In pbio (es_ids st ++ env_ids E) ->
    rw_cells ctasegs m out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 ->
    (forall b, In b K -> In b OW) -> (forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E)) -> (forall b, In b K -> blk_id b <> pbio) ->
    2 + sk_wire k <= W -> W <= MAX_SCT_LIST_SIZE ->                                  (* [comment removed for export] *)
    implAp (sct_list_print k st) Σ
           (ap_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E lo m K (CST (zlength (sk_items k))) (sct_print_resA st OW out pv))
           (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz SCT_LIST_PRINT_A) fc None m (seg_rom ctasegs)).

End WithRT.
