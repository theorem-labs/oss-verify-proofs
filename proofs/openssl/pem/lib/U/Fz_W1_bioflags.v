(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Ubs.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Layout. From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Th_kit Fz_T_kit. From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_W1_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition W1_bio_flags_stmt (ENTRY msk : Z) (upd : Z -> Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo BI fl : Z),
    a0 = Z_to_bv 64 BI -> a1 = Z_to_bv 64 msk -> 0 < BI -> BI mod 8 = 0 -> 0 <= fl < 2 ^ 31 ->
    rw_cells usegs m (BI + 48) [C4 (Z_to_bv 64 fl)] ->
    stk usegs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> BI + 52 <= lo ->
    mem_inv usegs m ->
    evt usegs (fun ms' => exists (a1' a2' : word) (m' : mem),
                 ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (ret_pc ra) fc None m' (seg_rom usegs)
                 /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (BI + 48, BI + 52)] m m'
                 /\ wmono usegs m m' /\ mem_inv usegs m'
                 /\ stk usegs m' lo (bv_unsigned sp)
                 /\ rw_cells usegs m' (BI + 48) [C4 (Z_to_bv 64 (upd fl))])
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 ENTRY) fc None m (seg_rom usegs)).

Theorem W1_bio_clear15_proof : W1_bio_flags_stmt 0x10bb2c 15 (fun fl => Z.land fl 18446744073709551600).
Proof.
  unfold W1_bio_flags_stmt. intros until fl. intros -> -> HBI HAL HFL FL ST LO0 LO SBI MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 16%nat [8; 8]%nat ST. do 3 ths.
  ths. ubs_if. ths. ths. ubs_if.
  ths. rewrite (t_sx32_small fl) by lia. ths. ths. ths.
  rewrite (unsigned_lit fl) in * by lia.
  do 2 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.

Theorem W1_bio_set9_proof : W1_bio_flags_stmt 0x10bb6c 9 (fun fl => Z.lor fl 9).
Proof.
  unfold W1_bio_flags_stmt. intros until fl. intros -> -> HBI HAL HFL FL ST LO0 LO SBI MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (BI + 48, BI + 52)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  ths. th_frame 16%nat [8; 8]%nat ST. do 3 ths.
  ths. ubs_if. ths. ths. ubs_if.
  ths. rewrite (t_sx32_small fl) by lia. ths. ths.
  rewrite (unsigned_lit fl) in * by lia.
  do 2 ths.
  lazymatch goal with FRh : rw_cells _ _ (bv_unsigned sp + -16) _ |- _ => th_release FRh (bv_unsigned sp) end.
  ths. ths. finish.
Qed.
