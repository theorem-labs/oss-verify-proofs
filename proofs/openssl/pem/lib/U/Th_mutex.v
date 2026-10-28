(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).
Notation z64 := (Z_to_bv 64 0) (only parsing).

(* [comment removed for export] *)
Definition mutex_cells (ty lk : word) : list cell := [C4 ty; C4 lk; C4 z64; C4 z64; C8 z64; C8 z64; C8 z64].

Definition mutexattr_destroy_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (ret_pc ra) fc None m (seg_rom usegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2be880) fc None m (seg_rom usegs)).

Theorem mutexattr_destroy_proof : mutexattr_destroy_stmt.
Proof.
  unfold mutexattr_destroy_stmt. intros. do 2 zstep. apply evt_done. reflexivity.
Qed.

Definition mutexattr_init_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (junk : list byte),
    rw_cells usegs m (bv_unsigned a0) [CB 4 junk] -> mem_inv usegs m ->
    evt usegs (fun ms' => exists m' : mem,
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned a0, bv_unsigned a0 + 4)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ rw_cells usegs m' (bv_unsigned a0) [C4 z64])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2be888) fc None m (seg_rom usegs)).

Theorem mutexattr_init_proof : mutexattr_init_stmt.
Proof.
  unfold mutexattr_init_stmt. intros until junk. intros FR MI.
  pose proof (rw_cells_bound _ _ _ _ FR) as FB. cbn [cells_size csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + 4)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Ap := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Ap) by (unfold Ap; rewrite Z_to_bv_bv_unsigned; reflexivity).
  do 3 zstep.
  apply evt_done. exists m0. split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI | exact FR].
Qed.

(* [comment removed for export] *)
Definition mutex_lock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells usegs m (bv_unsigned a0) (mutex_cells z64 z64) -> bv_unsigned a0 mod 4 = 0 -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned a0 + 4, bv_unsigned a0 + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ rw_cells usegs m' (bv_unsigned a0) (mutex_cells z64 (Z_to_bv 64 16)))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2be1ac) fc None m (seg_rom usegs)).

Theorem mutex_lock_proof : mutex_lock_stmt.
Proof.
  unfold mutex_lock_stmt. intros until m. intros MC AL MI.
  pose proof (rw_cells_bound _ _ _ _ MC) as FB. cbn [cells_size mutex_cells csize Nat.add] in FB.
  pose proof (munch_refl [(bv_unsigned a0 + 4, bv_unsigned a0 + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Ap := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Ap) by (unfold Ap; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (AMO : amo_aligned AW (Z_to_bv 64 (Ap + 4)) = true) by (apply th_amo_aligned; [lia|]; rewrite Z.add_mod by lia; rewrite AL; reflexivity).
  (* [comment removed for export] *)
  apply (th_cells_congr usegs m Ap _ ([C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C4 z64; C4 z64; C4 z64; C8 z64; C8 z64; C8 z64]))
    in MC; [| reflexivity | reflexivity | cbn; tauto].
  do 3 zstep. th_if_lit. do 2 zstep.
  th_amo_step AMO.
  zstep. th_if_lit.
  th_amo_step AMO.
  zstep. th_if_lit.
  zstep. zstep. th_if_lit.
  do 2 zstep.
  apply evt_done. do 5 eexists. exists m0.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
  apply (th_cells_congr usegs m0 Ap _ (mutex_cells z64 (Z_to_bv 64 16))) in MC; [exact MC | reflexivity | reflexivity | cbn; tauto].
Qed.

(* [comment removed for export] *)
Definition mutex_unlock_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
    rw_cells usegs m (bv_unsigned a0) (mutex_cells z64 (Z_to_bv 64 16)) -> bv_unsigned a0 mod 4 = 0 ->
    stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 ->
    (bv_unsigned a0 + 40 <= bv_unsigned sp - 96 \/ bv_unsigned sp <= bv_unsigned a0) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned a0 + 4, bv_unsigned a0 + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' (bv_unsigned a0) (mutex_cells z64 z64))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2be698) fc None m (seg_rom usegs)).

Theorem mutex_unlock_proof : mutex_unlock_stmt.
Proof.
  unfold mutex_unlock_stmt. intros until lo. intros MC AL ST LO SEP MI.
  pose proof (rw_cells_bound _ _ _ _ MC) as FB. cbn [cells_size mutex_cells csize Nat.add] in FB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (bv_unsigned a0 + 4, bv_unsigned a0 + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Ap := bv_unsigned a0) in *.
  replace a0 with (Z_to_bv 64 Ap) by (unfold Ap; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (AMO : amo_aligned AW (Z_to_bv 64 (Ap + 4)) = true) by (apply th_amo_aligned; [lia|]; rewrite Z.add_mod by lia; rewrite AL; reflexivity).
  unfold mutex_cells in MC.
  carve_frame 96%nat ST.
  do 12 step.
  do 6 step. th_if_lit.
  do 3 step.
  th_amo_step AMO. step. th_if_lit.
  th_amo_step AMO. step. th_if_lit.
  do 2 step. th_if_lit.
  do 4 step. th_if_lit. step. th_if_lit.
  do 14 step.
  release_frame FR ST (bv_unsigned sp).
  unfold mutex_cells. finish.
Qed.
