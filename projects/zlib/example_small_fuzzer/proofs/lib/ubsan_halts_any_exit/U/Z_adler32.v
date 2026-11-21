(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit Z_adler32.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Z_dkit Z_ukit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZChecksum DeflateLz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

Definition Z_ADLER32 : Z := 0x1aea4.
Definition Z_ADLER32_Z : Z := 0x1a974.
Definition ADLER32_FRAME : Z := 128.

Definition adler32_postU (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (v lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz v) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp).

Lemma adler32_z_len1_spec : forall (lo adler B c : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 <= adler < 2^64 -> 0 < B -> B + 1 <= lo -> 0 <= c < 256 ->
  bytes_at usegs m B [Z_to_bv 8 c] -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ADLER32_FRAME ->
  evt usegs (adler32_postU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_len1 adler c) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32_Z) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HA HB HBL HC BY MI STK LO. unfold Z_ADLER32_Z, ADLER32_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (proj1 STK) as LO0.
  assert (EC : bv_unsigned (Z_to_bv 8 c) = c) by (apply Z_to_bv_small; unfold bv_modulus; cbn; lia).
  assert (RA : 0 <= adler mod 65536 < 65536) by (apply Z.mod_pos_bound; lia).
  pose proof (srliw16 adler HA) as ES.
  set (sum2 := adler mod 2 ^ 32 / 2 ^ 16) in *.
  assert (RS2 : 0 <= sum2 < 65536).
  { subst sum2. split; [apply Z.div_pos; [apply Z.mod_pos_bound|]; lia|]. apply Z.div_lt_upper_bound; [lia|]. pose proof (Z.mod_pos_bound adler (2^32)); lia. }
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  carve_frame 128%nat STK.
  do 14 zs.
  pose proof (u8ro_read usegs _ B [Z_to_bv 8 c] 0 (Z_to_bv 8 c) (wa (B + 0)) BY eq_refl ltac:(lia) eq_refl) as RD.
  replace (B + 0) with B in RD by lia.
  zstep. rewrite ES.
  do 4 zstep. if_false. gF.
  do 6 zstep. rewrite EC.
  do 5 zstep. rewrite (csub_mask (adler mod 65536 + c)) by lia.
  set (a := adler_csub (adler mod 65536 + c)).
  assert (RAa : 0 <= a < 65792) by (subst a; unfold adler_csub; destruct (Z.ltb_spec 65520 (adler mod 65536 + c)); lia).
  do 9 zstep. rewrite (csub_mask16 (a + sum2)) by lia.
  do 14 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold adler32_postU. do 14 eexists. eexists.
  split; [unfold adler32_len1; fold sum2; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact STK].
Qed.

Lemma adler32_len1_spec : forall (lo adler B c : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 <= adler < 2^64 -> 0 < B -> B + 1 <= lo -> 0 <= c < 256 ->
  bytes_at usegs m B [Z_to_bv 8 c] -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ADLER32_FRAME ->
  evt usegs (adler32_postU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (adler32_len1 adler c) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz B) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HA HB HBL HC BY MI STK LO. unfold Z_ADLER32.
  do 3 zstep. apply (adler32_z_len1_spec lo); assumption.
Qed.

Lemma adler32_null_spec : forall (lo adler len : Z) ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) (fc : bv 32) (m : mem),
  0 <= adler < 2^64 -> 0 <= len < 2^32 -> len <> 1 -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ADLER32_FRAME ->
  evt usegs (adler32_postU ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 1 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz adler) (wz 0) (wz len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz Z_ADLER32) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HA HL HN MI STK LO. unfold Z_ADLER32, ADLER32_FRAME in *.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (proj1 STK) as LO0.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
  do 3 zstep.
  carve_frame 128%nat STK.
  do 14 zs.
  do 5 zstep.
  if_cases K; zify_cond K.
  2:{ exfalso. rewrite ?Z.mod_small in K by lia. lia. }
  zstep. if_true.
  do 14 zs. release_frame FR STK (bv_unsigned sp). zs.
  apply evt_done. unfold adler32_postU. do 14 eexists. eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption| exact STK].
Qed.
