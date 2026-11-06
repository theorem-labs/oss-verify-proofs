(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import XL_mutex.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition P_B_SLOCK_DTOR   : Z := 0xa7c64.
Definition P_B_SLOCK_UNLOCK : Z := 0xb52d8.
Definition P_B_SLOCK_LOCK   : Z := 0xb5388.
Definition ASLOCK_DTOR_STACK   : Z := 16 + MUTEX_UNLOCK_STACK.
Definition ASLOCK_UNLOCK_STACK : Z := 32 + MUTEX_UNLOCK_STACK.
Definition ASLOCK_LOCK_STACK   : Z := 32.

Section HCW.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)
Definition slock_dtor_post (ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (M lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (M, M + 40)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ APMutex m' M 0.

Definition slock_dtor_stmt : Prop :=
  forall (SL M lo shi : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells bsegs m SL [C8 (wz M)] -> ro_cells bsegs m (SL + 8) [C1 (b8 1)] ->
  APMutex m M EBUSY -> 0 < M -> M mod 8 = 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ASLOCK_DTOR_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned sp <= SL -> SL + 16 <= shi -> SL mod 8 = 0 ->
  aapp M 40 ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi ->
  evt bsegs (slock_dtor_post ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc M lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz SL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_B_SLOCK_DTOR) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition slock_unlock_post (ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (SL M lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (SL + 8, SL + 9); (M, M + 40)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (SL + 8) [C1 (b8 0)]
    /\ APMutex m' M 0.

Definition slock_unlock_stmt : Prop :=
  forall (SL M lo shi : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells bsegs m SL [C8 (wz M)] -> rw_cells bsegs m (SL + 8) [C1 (b8 1)] ->
  APMutex m M EBUSY -> 0 < M -> M mod 8 = 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ASLOCK_UNLOCK_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned sp <= SL -> SL + 16 <= shi -> SL mod 8 = 0 ->
  aapp M 40 ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi ->
  evt bsegs (slock_unlock_post ra sp gp tp s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc SL M lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz SL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_B_SLOCK_UNLOCK) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition slock_lock_post (ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (SL M lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a0 a1 a2 a3 a4 a5 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(lo, bv_unsigned sp); (SL + 8, SL + 9); (M, M + 40)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (SL + 8) [C1 (b8 1)]
    /\ APMutex m' M EBUSY.

Definition slock_lock_stmt : Prop :=
  forall (SL M lo shi : Z) ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  ro_cells bsegs m SL [C8 (wz M)] -> rw_cells bsegs m (SL + 8) [C1 (b8 0)] ->
  APMutex m M 0 -> 0 < M -> M mod 8 = 0 ->
  stk bsegs m lo (bv_unsigned sp) -> lo + ASLOCK_LOCK_STACK <= bv_unsigned sp -> aceil <= lo ->
  bv_unsigned sp <= SL -> SL + 16 <= shi -> SL mod 8 = 0 ->
  aapp M 40 ->
  bv_unsigned ra mod 2 = 0 ->
  mem_inv bsegs m ->
  (* [comment removed for export] *)
  ACONST m -> stack0 m lo shi ->
  evt bsegs (slock_lock_post ra sp gp tp s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 F fc SL M lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz SL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 P_B_SLOCK_LOCK) fc None m (seg_rom bsegs)).

End HCW.
