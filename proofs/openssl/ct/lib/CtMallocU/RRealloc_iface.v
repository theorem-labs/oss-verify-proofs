(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.openssl.ct.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocHINV Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog LibProg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition RREALLOC_SYM : Z := 0x2b4f58.     (* [comment removed for export] *)
Definition rrealloc_entry : Z := 0x2b4f5c.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition RREALLOC_STACK : Z := 8192 + 64.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rmalloc_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ctusegs (raw_malloc n) s
        (rmalloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom ctusegs)).

Definition rfree_impl_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A ->
  implM ctusegs (raw_free p) s
        (rfree_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition rrealloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (old : list byte) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rw_cells ctusegs m' A [CB (Z.to_nat n0) old]
       | Some q => exists A' junk,
           a0 = Z_to_bv 64 A' /\ rblock_range A' n
           /\ RHEAP s' ((q, A', n) :: lb_remove p LB) m'
           /\ rw_cells ctusegs m' A' [CB (Z.to_nat n0) old; CB (Z.to_nat (n - n0)) junk]
           /\ n0 < n
       end.

Definition rrealloc_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old : list byte),
  RHEAP s LB m -> In (p, A, n0) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  rw_cells ctusegs m A [CB (Z.to_nat n0) old] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  implM ctusegs (raw_realloc p n) s
        (rrealloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition rrealloc_shrink_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (old : list byte) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ match r with
       | None => a0 = Z_to_bv 64 0 /\ RHEAP s' LB m' /\ rw_cells ctusegs m' A [CB (Z.to_nat n0) old]
       | Some q => exists A',
           a0 = Z_to_bv 64 A' /\ rblock_range A' n
           /\ RHEAP s' ((q, A', n) :: lb_remove p LB) m'
           /\ rw_cells ctusegs m' A' [CB (Z.to_nat n) (firstn (Z.to_nat n) old)]
           /\ n < n0
       end.

Definition rrealloc_shrink_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old : list byte),
  RHEAP s LB m -> In (p, A, n0) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  rw_cells ctusegs m A [CB (Z.to_nat n0) old] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n < n0 ->
  implM ctusegs (raw_realloc_shrink p n) s
        (rrealloc_shrink_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom ctusegs)).

(* [comment removed for export] *)
Definition rrealloc_inplace_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (old : list byte) (m : mem)
    (r : option bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
    /\ rw_cells ctusegs m' (errno_addr tp) [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres (lb_remove p LB) (bv_unsigned sp) m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ r = Some p /\ s' = s /\ a0 = Z_to_bv 64 A
    /\ RHEAP s ((p, A, n) :: lb_remove p LB) m'
    /\ rw_cells ctusegs m' A [CB (Z.to_nat n) (firstn (Z.to_nat n) old)].

Definition rrealloc_inplace_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (p : bptr) (A n0 n lo B : Z) (errv : word) (old : list byte),
  RHEAP s LB m -> In (p, A, n0) LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ctusegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ctusegs m (errno_addr tp) [C4 errv] ->
  rw_cells ctusegs m A [CB (Z.to_nat n0) old] ->
  mem_inv ctusegs m ->
  tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> 0 <= n <= n0 ->
  implM ctusegs (raw_realloc_inplace p n) s
        (rrealloc_inplace_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p A n0 n lo B old m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 RREALLOC_SYM) fc None m (seg_rom ctusegs)).

End WithCeiling0.
