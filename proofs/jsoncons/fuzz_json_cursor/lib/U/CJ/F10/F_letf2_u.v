(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Spec Require Import SoftFloat.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition rsegs := Ubsan.Ubsan_loaded_segments.

Definition letf2_entry := 0xafb4c%Z.

Definition f128_isnan_w (lo hi : Z) : bool :=
  (let absHi := Z.land hi ABS_HI in
   if absHi =? INF_HI then negb (lo =? 0) else INF_HI <? absHi)%Z.

Definition f128_le_isless (a_lo a_hi b_lo b_hi : Z) : bool :=
  (if negb (is_neg64 (Z.land b_hi a_hi)) then
     (if a_hi =? b_hi then a_lo <? b_lo else lt_s64 a_hi b_hi)
   else
     (if a_hi =? b_hi then b_lo <? a_lo else lt_s64 b_hi a_hi))%Z.

Definition f128_le_tail (il : bool) (a_lo a_hi b_lo b_hi : Z) : Z :=
  if il then (-1)%Z else nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)).

Definition f128_le_core (a_lo a_hi b_lo b_hi : Z) : Z :=
  (if Z.lor (Z.lor b_lo a_lo) (Z.lor (Z.land b_hi ABS_HI) (Z.land a_hi ABS_HI)) =? 0 then 0
   else f128_le_tail (f128_le_isless a_lo a_hi b_lo b_hi) a_lo a_hi b_lo b_hi)%Z.

Lemma lo64_words : forall lo hi, (0 <= lo < 2^64)%Z -> lo64 (lo + 2^64 * hi) = lo.
Proof.
  intros lo hi H. unfold lo64. rewrite wrap64_mod.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma hi64_words : forall lo hi, (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z -> hi64 (lo + 2^64 * hi) = hi.
Proof.
  intros lo hi Hl Hh. unfold hi64. rewrite wrap64_mod, Z.shiftr_div_pow2 by lia.
  rewrite Z.mul_comm, Z.div_add, Z.div_small by lia. apply Z.mod_small. lia.
Qed.

Lemma f128_le_split : forall a_lo a_hi b_lo b_hi,
  (0 <= a_lo < 2^64)%Z -> (0 <= a_hi < 2^64)%Z -> (0 <= b_lo < 2^64)%Z -> (0 <= b_hi < 2^64)%Z ->
  f128_le (a_lo + 2^64 * a_hi) (b_lo + 2^64 * b_hi) =
  if f128_isnan_w a_lo a_hi then 1%Z
  else if f128_isnan_w b_lo b_hi then 1%Z
  else f128_le_core a_lo a_hi b_lo b_hi.
Proof.
  intros. unfold f128_le. rewrite !lo64_words, !hi64_words by assumption. reflexivity.
Qed.

Lemma b2z_snez : forall x, (0 <= x)%Z -> Z.b2z (0 <? x)%Z = nez64 x.
Proof.
  intros x Hx. unfold nez64, b2z. destruct (Z.ltb_spec0 0 x); destruct (Z.eqb_spec x 0); cbn; lia.
Qed.

Definition letf2_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Hypothesis MI : mem_inv rsegs m.
  Let MU : munch [] m m := munch_refl [] m.
  Let WM : wmono rsegs m m := wmono_refl rsegs m.

  Notation a_lo := (bv_unsigned a0). Notation a_hi := (bv_unsigned a1).
  Notation b_lo := (bv_unsigned a2). Notation b_hi := (bv_unsigned a3).
  Notation POST r := (letf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m).

  Notation ST pc x14 x15 x16 x17 :=
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Notation M63 := 9223372036854775807%Z.

  Lemma letf2_L98 : forall (a4 a5 a6 a7 : word) (r : Z),
    r = nez64 (Z.lor (Z.lxor a_lo b_lo) (Z.lxor a_hi b_hi)) ->
    evt rsegs (POST r) (ST 0xafc00 a4 a5 a6 a7).
  Proof using MI.
    intros a4 a5 a6 a7 r HR. subst r.
    do 5 zstep. rewrite b2z_snez by zrange_nonneg. finish.
  Qed.

  Lemma letf2_L40 : forall (a4 a7 : word) (r : Z),
    r = f128_le_core a_lo a_hi b_lo b_hi ->
    evt rsegs (POST r) (ST 0xafba8 a4 (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 (Z.land b_hi M63)) a7).
  Proof using MI.
    intros a4 a7 r HR. subst r. unfold f128_le_core, ABS_HI.
    zr_pose (Z.land b_hi a_hi).
    do 4 zstep.
    if_cases Kz; zify_cond Kz.
    -
      zstep. zstep. decide_tests_b.
      match goal with |- context [Z_to_bv 64 (Z.lor ?x ?y)] => replace (Z.lor x y) with 0%Z by (symmetry; exact Kz) end.
      finish.
    - decide_tests_b. unfold f128_le_isless, f128_le_tail, is_neg64, lt_s64, SIGN64.
      zstep. zstep. if_cases Kn; zify_cond Kn; decide_tests_b.
      +
        zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
        *   zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
          -- apply letf2_L98. reflexivity.
          -- zstep. zstep. finish.
        * zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
          -- zstep. zstep. finish.
          -- zstep. apply letf2_L98. reflexivity.
      + zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
        * zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
          -- apply letf2_L98. reflexivity.
          -- zstep. zstep. finish.
        * zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
          -- zstep. zstep. finish.
          -- zstep. apply letf2_L98. reflexivity.
  Qed.

  Lemma letf2_L1c : forall (a7 : word) (r : Z),
    r = (if f128_isnan_w b_lo b_hi then 1%Z else f128_le_core a_lo a_hi b_lo b_hi) ->
    evt rsegs (POST r) (ST 0xafb84 (Z_to_bv 64 1) (Z_to_bv 64 (Z.land a_hi M63)) (Z_to_bv 64 M63) a7).
  Proof using MI.
    intros a7 r HR. unfold f128_isnan_w, ABS_HI, INF_HI in HR.
    do 4 zstep.
    if_cases K; zify_cond K.
    -
      zstep. zstep. if_cases Kl; zify_cond Kl.
      +   rewrite HR. decide_tests_b. zstep. zstep. finish.
      + apply letf2_L40. rewrite HR. decide_tests_b. reflexivity.
    - zstep. zstep. if_cases Kl; zify_cond Kl.
      + apply letf2_L40. rewrite HR. decide_tests_b. reflexivity.
      + rewrite HR. decide_tests_b. zstep. zstep. zstep. finish.
  Qed.
End Proofs.

Lemma letf2_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv rsegs m ->
  evt rsegs (letf2_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               (f128_le (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xafb4c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rewrite f128_le_split by (pose proof (bv_unsigned_in_range 64 a0); pose proof (bv_unsigned_in_range 64 a1);
                            pose proof (bv_unsigned_in_range 64 a2); pose proof (bv_unsigned_in_range 64 a3);
                            unfold bv_modulus in *; lia).
  remember (if f128_isnan_w (bv_unsigned a0) (bv_unsigned a1) then _ else _) as r eqn:HR.
  unfold f128_isnan_w at 1, ABS_HI, INF_HI in HR.
  do 6 zstep.
  if_cases K; zify_cond K.
  -
    do 3 zstep. if_cases Kl; zify_cond Kl.
    + rewrite HR. decide_tests_b. zstep. zstep. finish.
    + apply letf2_L1c; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
  - do 3 zstep. if_cases Kl; zify_cond Kl.
    + apply letf2_L1c; [exact MI|]. rewrite HR. decide_tests_b. reflexivity.
    + rewrite HR. decide_tests_b. zstep. zstep. finish.
Qed.
