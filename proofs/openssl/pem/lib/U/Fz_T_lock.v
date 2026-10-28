(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Th_mutex. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition T_lock_stmt (LK : Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    rw_cells usegs m (bv_unsigned a0) (mutex_cells z64 z64) -> bv_unsigned a0 mod 4 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 40 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->      (* [comment removed for export] *)
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0 + 4, bv_unsigned a0 + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' (bv_unsigned a0) (mutex_cells z64 (Z_to_bv 64 16)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 LK) fc None m (seg_rom usegs)).

Ltac t_lock_script sp a0 m MC ST :=
  let FB := fresh "FB" in let RSP := fresh "RSP" in let MU := fresh "MU" in let WM := fresh "WM" in
  pose proof (rw_cells_bound _ _ _ _ MC) as FB; cbn [cells_size mutex_cells csize Nat.add] in FB;
  pose proof (bv_unsigned_in_range 64 sp) as RSP; unfold bv_modulus in RSP; cbn in RSP;
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0 + 4, bv_unsigned a0 + 8)]%Z m) as MU;
  pose proof (wmono_refl usegs m) as WM;
  unfold mutex_cells in MC;
  th_frame 16%nat [8; 8]%nat ST;
  do 5 ths;
  call (mutex_lock_proof); [ first [eassumption | lia] .. | ];
  cbv delta [mkR];
  do 5 ths;
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => release_frame FRh ST (bv_unsigned sp) end;
  finish.

Theorem T_read_lock_proof : T_lock_stmt 0xe3870.
Proof. unfold T_lock_stmt. intros until lo. intros MC AL ST LO0 LO SEP MI. t_lock_script sp a0 m MC ST. Qed.

Theorem T_write_lock_proof : T_lock_stmt 0xe389c.
Proof. unfold T_lock_stmt. intros until lo. intros MC AL ST LO0 LO SEP MI. t_lock_script sp a0 m MC ST. Qed.

(* [comment removed for export] *)
Definition T_unlock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    rw_cells usegs m (bv_unsigned a0) (mutex_cells z64 (Z_to_bv 64 16)) -> bv_unsigned a0 mod 4 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 112 ->
    (bv_unsigned a0 + 40 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0 + 4, bv_unsigned a0 + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' (bv_unsigned a0) (mutex_cells z64 z64))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe38c8) fc None m (seg_rom usegs)).

Theorem T_unlock_proof : T_unlock_stmt.
Proof.
  unfold T_unlock_stmt. intros until lo. intros MC AL ST LO0 LO SEP MI.
  pose proof (rw_cells_bound _ _ _ _ MC) as FB. cbn [cells_size mutex_cells csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (bv_unsigned a0 + 4, bv_unsigned a0 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold mutex_cells in MC.
  th_frame 16%nat [8; 8]%nat ST.
  do 5 ths.
  pose proof mutex_unlock_proof as UL. unfold mutex_unlock_stmt in UL.
  specialize (UL (Z_to_bv 64 0xe38e0) (Z_to_bv 64 (bv_unsigned sp + -16))).
  rewrite (unsigned_lit (bv_unsigned sp + -16)) in UL by lia.
  call (UL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo).
  1-6: first [eassumption | lia].
  cbv delta [mkR].
  do 5 ths.
  lazymatch goal with STh : stk _ _ _ _ |- _ => release_frame FR STh (bv_unsigned sp) end.
  finish.
Qed.
