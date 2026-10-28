(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocBlocks Malloc_iface ClientOwn LhPure.
From OssFuzzTheorems.Proofs.openssl.pem.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout Fz_iface Driver_iface Drv_kit Fz_kit Fz_M_realloc Fz_kit_ra Fz_T_sk.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import CeilWin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition SK_PUSH_ROOM_STACK : Z := 112.
Definition T_sk_push_room_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A D num nalloc s01 : Z) (pad cmpt freet copyt : word) (junk : list byte),
    a0 = Z_to_bv 64 A -> 0 < A -> 0 < D ->
    rw_cells usegs m A (sk_cells (Z_to_bv 64 num) pad (Z_to_bv 64 D) (Z_to_bv 64 s01) (Z_to_bv 64 nalloc) z64 cmpt freet copyt) ->
    (s01 = 0 \/ s01 = 1) -> 1 <= num -> num + 1 <= nalloc -> 4 <= nalloc < 2 ^ 20 ->
    rw_cells usegs m D [CB (Z.to_nat (8 * nalloc)) junk] -> A mod 8 = 0 -> D mod 8 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - SK_PUSH_ROOM_STACK ->
    A + 56 <= lo -> D + 8 * nalloc <= lo -> (A + 56 <= D \/ D + 8 * nalloc <= A) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk' : list byte) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (num + 1)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - SK_PUSH_ROOM_STACK, bv_unsigned sp); (A, A + 56); (D, D + 8 * nalloc)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' A (sk_cells (Z_to_bv 64 (num + 1)) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 nalloc) z64 cmpt freet copyt)
                 /\ rw_cells usegs m' D [CB (Z.to_nat (8 * nalloc)) junk'])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FZ_SK_PUSH) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
Definition SK_PUSH_GROW_STACK : Z := 96 + CRE_STACK.   (* [comment removed for export] *)
Definition sk_push_grow_res (psk pd : bptr) (A D : Z) (pad cmpt freet copyt : word) (src : list byte) (LBall : list block) (L : @clist bptr)
    : word -> list block -> @clist bptr -> mem -> Prop :=
  fun v LBall' L' m' => exists (q : bptr) (D' : Z) (junk' : list byte),
       v = Z_to_bv 64 5 /\ LBall' = (q, D', 48) :: lb_remove pd LBall /\ rblock_range D' 48
    /\ rw_cells usegs m' A (sk_cells (Z_to_bv 64 5) pad (Z_to_bv 64 D') z64 (Z_to_bv 64 6) z64 cmpt freet copyt)
    /\ rw_cells usegs m' D' [CB 48%nat junk']
    /\ ((q = pd /\ D' = D /\ L' = L) \/ (exists i, nth_error L i = Some (pd, 32) /\ L' = (q, 48) :: cremove i L)).
Definition T_sk_push_grow_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : PState) (LBall LB : list block) (L : @clist bptr) (f : nat) (lo B : Z)
         (psk pd : bptr) (A D : Z) (pad cmpt freet copyt : word) (src : list byte),
    (2 <= f)%nat -> croom L (wA 48) (wB 48) (wBig 48) ->
    cstate st LBall LB L m sp tp lo B -> lo <= bv_unsigned sp - SK_PUSH_GROW_STACK -> a0 = Z_to_bv 64 A ->
    In (psk, A, 56) LBall -> cown LBall L pd D 32 32 -> psk <> pd ->
    rw_cells usegs m A (sk_cells (Z_to_bv 64 4) pad (Z_to_bv 64 D) z64 (Z_to_bv 64 4) z64 cmpt freet copyt) ->
    rw_cells usegs m D [CB 32%nat src] ->
    climpl f L st (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 FZ_SK_PUSH) fc None m (seg_rom usegs))
           (cpost ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LBall LB L f m lo B (fun q => q = psk \/ q = pd) [] 2 (wA 48) (wB 48) (wBig 48)
                  (sk_push_grow_res psk pd A D pad cmpt freet copyt src LBall L)).
End WithCeiling0.
