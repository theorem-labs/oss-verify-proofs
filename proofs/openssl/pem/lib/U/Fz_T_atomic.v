(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition T_atomic_load_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (v old : word),
    ro_cells usegs m (bv_unsigned a0) [C8 v] ->
    rw_cells usegs m (bv_unsigned a1) [C8 old] ->
    (bv_unsigned a0 + 8 <= bv_unsigned a1 \/ bv_unsigned a1 + 8 <= bv_unsigned a0) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a1 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a1) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ ro_cells usegs m' (bv_unsigned a0) [C8 v]
                 /\ rw_cells usegs m' (bv_unsigned a1) [C8 v])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3af4) fc None m (seg_rom usegs)).

Theorem T_atomic_load_proof : T_atomic_load_stmt.
Proof.
  unfold T_atomic_load_stmt. intros until old. intros VC RC SEP ST LO0 LO S1 S2 MI.
  pose proof (ro_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (rw_cells_bound _ _ _ _ RC) as RB. cbn [cells_size csize Nat.add] in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  set (Vp := bv_unsigned a0) in *. set (Rp := bv_unsigned a1) in *.
  replace a0 with (Z_to_bv 64 Vp) by (unfold Vp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  replace a1 with (Z_to_bv 64 Rp) by (unfold Rp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths.
  do 4 ths.
  do 4 ths.
  th_release FR (bv_unsigned sp).
  finish.
Qed.

Lemma t_amo_aligned8 : forall a : Z, 0 <= a < 2 ^ 64 -> a mod 8 = 0 -> amo_aligned AD (Z_to_bv 64 a) = true.
Proof. intros a Ha Hm. unfold amo_aligned, amo_bytes. rewrite unsigned_lit by lia. rewrite Hm. reflexivity. Qed.

Lemma t_amo_or : forall v a : word, amo_val AMO_OR v a = Z_to_bv 64 (Z.lor (bv_unsigned v) (bv_unsigned a)).
Proof.
  intros v a. unfold amo_val. apply bv_eq. rewrite Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 (bv_or v a)) as R. rewrite bv_or_unsigned in *.
  symmetry. apply bv_wrap_small. exact R.
Qed.

(* [comment removed for export] *)
Definition T_atomic_or_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (v old : word),
    rw_cells usegs m (bv_unsigned a0) [C8 v] -> bv_unsigned a0 mod 8 = 0 ->
    rw_cells usegs m (bv_unsigned a2) [C8 old] -> bv_unsigned a2 <> 0 -> bv_unsigned a2 mod 8 = 0 ->
    (bv_unsigned a0 + 8 <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= bv_unsigned a0) ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 ->
    (bv_unsigned a0 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a0) ->
    (bv_unsigned a2 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a2) ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (nv a3' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) nv a2 a3' a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 8); (bv_unsigned a2, bv_unsigned a2 + 8)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ nv = Z_to_bv 64 (Z.lor (bv_unsigned v) (bv_unsigned a1))
                 /\ rw_cells usegs m' (bv_unsigned a0) [C8 nv]
                 /\ rw_cells usegs m' (bv_unsigned a2) [C8 nv])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0xe3ab4) fc None m (seg_rom usegs)).

Theorem T_atomic_or_proof : T_atomic_or_stmt.
Proof.
  unfold T_atomic_or_stmt. intros until old. intros VC AL RC NZ RAL SEP ST LO0 LO S1 S2 MI.
  pose proof (rw_cells_bound _ _ _ _ VC) as VB. cbn [cells_size csize Nat.add] in VB.
  pose proof (rw_cells_bound _ _ _ _ RC) as RB. cbn [cells_size csize Nat.add] in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (bv_unsigned a0, bv_unsigned a0 + 8); (bv_unsigned a2, bv_unsigned a2 + 8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  set (Vp := bv_unsigned a0) in *. set (Rp := bv_unsigned a2) in *.
  replace a0 with (Z_to_bv 64 Vp) by (unfold Vp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  replace a2 with (Z_to_bv 64 Rp) by (unfold Rp; rewrite Z_to_bv_bv_unsigned; reflexivity).
  assert (AMO : amo_aligned AD (Z_to_bv 64 Vp) = true) by (apply t_amo_aligned8; [lia | exact AL]).
  th_frame 16%nat [8; 8]%nat ST.
  do 4 ths.
  th_amo_step AMO. rewrite t_amo_or in VC.
  ths. ubs_if. ths. ths. ubs_if.
  do 3 ths.
  do 4 ths.
  th_release FR (bv_unsigned sp).
  apply evt_done. exists (Z_to_bv 64 (Z.lor (bv_unsigned v) (bv_unsigned a1))). eexists. exists m1.
  split; [cbv delta [mkR]; reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
  split; [reflexivity|]. split; [exact VC | exact RC].
Qed.
