(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import F_f128_mul_core1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Image.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition multf3_entry := 0xc8a8c%Z.
Definition multf3_core_pc := 0xc8b0c%Z.
Definition multf3_mid_pc := 0xc8c98%Z.

Lemma mulhu_shl32 : forall x y, 0 <= x -> 0 <= y ->
  Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615 * Z.land (Z.shiftl y 32) 18446744073709551615) 64
  = Z.land (Z.land x 4294967295 * Z.land y 4294967295) 18446744073709551615.
Proof.
  intros x y Hx Hy.
  rewrite !land_W64. change 4294967295 with (2^32 - 1). rewrite !zb_land_mask by lia.
  rewrite !Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^64) with (2^32 * 2^32) at 1 2.
  rewrite !Zmult_mod_distr_r.
  pose proof (Z.mod_pos_bound x (2^32) ltac:(lia)). pose proof (Z.mod_pos_bound y (2^32) ltac:(lia)).
  replace (x mod 2^32 * 2^32 * (y mod 2^32 * 2^32)) with ((x mod 2^32 * (y mod 2^32)) * 2^64) by lia.
  rewrite Z.div_mul by lia. symmetry. apply Z.mod_small. nia.
Qed.

Definition multf3_mid (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (aExp bExp aSigHi aSigLo bSigHi bSigLo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists es hh hl lh ll y5' t1 t2' x8 x9 a5' a6' s2' s3' s4' s5' s6' s7' s8' t3 t4 t5 t6,
    (forall signHi scale, mul_core signHi aExp bExp aSigHi aSigLo bSigHi bSigLo scale = MC_tail signHi es hh hl lh ll scale)
    /\ (0 <= es < 65536)%Z /\ (0 <= hh < 2^64)%Z /\ (0 <= hl < 2^64)%Z /\ (0 <= lh < 2^64)%Z /\ (0 <= ll < 2^64)%Z /\
    y5' = Z_to_bv 64 es /\ a5' = Z_to_bv 64 18446744073709551615 /\ a6' = Z_to_bv 64 281474976710655 /\ t2' = Z_to_bv 64 (-16383) /\
    ms' = MS (mkR ra sp gp tp y5' t1 t2' x8 x9
                 a0 a1 (Z_to_bv 64 ll) (Z_to_bv 64 lh) (Z_to_bv 64 hh) a5' a6' (Z_to_bv 64 hl)
                 s2' s3' s4' s5' s6' s7' s8' s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0xc8c98) fc None m (seg_rom usegs).

Lemma multf3_core1 : forall (ra sp gp tp w1 w2 s0 s1 a0 a1 w4 a3 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w3 t5 t6 : word) (ea eb : Z)
    (F : bvmap 5 word) fc (m : word -> option byte),
  mem_inv usegs m ->
  (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z ->
  evt usegs (multf3_mid ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
               ea eb (bv_unsigned w1) (bv_unsigned w3) (bv_unsigned w2) (bv_unsigned w4) m)
    (MS (mkR ra sp gp tp (Z_to_bv 64 eb) w1 w2 s0 s1 a0 a1 w4 a3 a4 (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 281474976710655) (Z_to_bv 64 ea)
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (Z.shiftr (bv_unsigned w1) 32)) w3 t5 t6)
        F (Z_to_bv 64 0xc8b0c) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros MI He1 He2.
  pose_word_ranges.
  set (aExp := ea) in *. set (bExp := eb) in *.
  set (aSigHi := bv_unsigned w1) in *. set (aSigLo := bv_unsigned w3) in *. set (bSigHi := bv_unsigned w2) in *. set (bSigLo := bv_unsigned w4) in *.

  do 1 zstep. model_reg 13 bLo15 (Z.land (Z.shiftl bSigLo 15) 18446744073709551615).
  do 6 zstep. model_reg 12 A3 (Z.shiftr aSigLo 32).
  do 2 zstep. model_reg 5 expSum (Z.land (aExp + bExp) 18446744073709551615).
  do 2 zstep. model_reg 28 A1 (Z.lor (Z.shiftr aSigHi 32) 65536).
  do 3 zstep. model_reg 14 bHi15 (Z.lor (Z.shiftr bSigLo 49) (Z.land (Z.shiftl bSigHi 15) 18446744073709551615)).
  do 1 zstep. model_reg 8 B3 (Z.shiftr bLo15 32).
  do 2 zstep. model_reg 9 A2 (Z.land aSigHi 4294967295).
  do 1 zstep. model_reg 18 A4 (Z.land aSigLo 4294967295).
  do 2 zstep. model_reg 17 B1 (Z.lor (Z.shiftr (Z.land (Z.shiftl bSigHi 15) 18446744073709551615) 32) 2147483648).
  do 2 zstep. model_reg 30 p13 (Z.land (B3 * A1) 18446744073709551615).
  do 1 zstep. model_reg 31 B4 (Z.land bLo15 4294967295).
  do 1 zstep. model_reg 19 p23 (Z.land (B3 * A2) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bLo15 4294967295) with B4. change (Z.land aSigHi 4294967295) with A2.
  model_reg 20 p24 (Z.land (B4 * A2) 18446744073709551615).
  do 1 zstep. model_reg 21 p33 (Z.land (B3 * A3) 18446744073709551615).
  do 1 zstep. model_reg 8 p43 (Z.land (B3 * A4) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bLo15 4294967295) with B4. change (Z.land aSigLo 4294967295) with A4.
  model_reg 13 p44 (Z.land (B4 * A4) 18446744073709551615).
  do 1 zstep. model_reg 22 p11 (Z.land (B1 * A1) 18446744073709551615).
  do 1 zstep. model_reg 23 B2 (Z.land bHi15 4294967295).
  do 1 zstep. model_reg 24 p14 (Z.land (B4 * A1) 18446744073709551615).
  do 1 zstep. model_reg 9 p21 (Z.land (B1 * A2) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bHi15 4294967295) with B2. change (Z.land aSigHi 4294967295) with A2.
  model_reg 6 p22 (Z.land (B2 * A2) 18446744073709551615).
  do 1 zstep. model_reg 18 p41 (Z.land (B1 * A4) 18446744073709551615).
  do 1 zstep. model_reg 17 p31 (Z.land (B1 * A3) 18446744073709551615).
  do 1 zstep. model_reg 31 p34 (Z.land (B4 * A3) 18446744073709551615).
  do 1 zstep. rewrite mulhu_shl32 by zrange_nonneg. change (Z.land bHi15 4294967295) with B2. change (Z.land aSigLo 4294967295) with A4.
  model_reg 14 p42 (Z.land (B2 * A4) 18446744073709551615).
  do 1 zstep. model_reg 21 s2a (Z.land (p24 + p33) 18446744073709551615).
  do 1 zstep. model_reg 28 p12 (Z.land (B2 * A1) 18446744073709551615).
  do 1 zstep. model_reg 12 p32 (Z.land (B2 * A3) 18446744073709551615).
  do 1 zstep. model_reg 8 sum1 (Z.land (p34 + p43) 18446744073709551615).
  do 1 zstep. model_reg 29 c2a (Z.b2z (s2a <? p24)).
  do 1 zstep. model_reg 14 sum2 (Z.land (s2a + p42) 18446744073709551615).
  do 1 zstep. model_reg 19 s3a (Z.land (p14 + p23) 18446744073709551615).
  do 1 zstep. model_reg 30 s4a (Z.land (p31 + p13) 18446744073709551615).
  do 1 zstep. model_reg 31 c1 (Z.b2z (sum1 <? p34)).
  do 1 zstep. model_reg 20 c2b (Z.b2z (sum2 <? s2a)).
  do 1 zstep. model_reg 21 c3a (Z.b2z (s3a <? p14)).
  do 1 zstep. model_reg 18 s3b (Z.land (s3a + p41) 18446744073709551615).
  do 1 zstep. model_reg 9 sum5 (Z.land (p12 + p21) 18446744073709551615).
  do 1 zstep. model_reg 23 sum1Shr32 (Z.shiftr sum1 32).
  do 1 zstep. model_reg 8 sum1Shl32 (Z.land (Z.shiftl sum1 32) 18446744073709551615).
  do 1 zstep. model_reg 17 c4a (Z.b2z (s4a <? p31)).
  do 1 zstep. model_reg 6 sum4 (Z.land (s4a + p22) 18446744073709551615).
  do 1 zstep. model_reg 29 sum2Hi (Z.land (c2a + c2b) 18446744073709551615).
  do 1 zstep. model_reg 19 c3b (Z.b2z (s3b <? s3a)).
  do 1 zstep. model_reg 20 sum3 (Z.land (s3b + p32) 18446744073709551615).
  do 1 zstep. model_reg 28 c5 (Z.b2z (sum5 <? p12)).
  do 1 zstep. model_reg 31 c1Shl32 (Z.land (Z.shiftl c1 32) 18446744073709551615).
  do 1 zstep. model_reg 12 lo_lo (Z.land (sum1Shl32 + p44) 18446744073709551615).
  do 1 zstep. model_reg 13 sum5Shr32 (Z.shiftr sum5 32).
  do 1 zstep. model_reg 9 sum5Shl32 (Z.land (Z.shiftl sum5 32) 18446744073709551615).
  do 1 zstep. model_reg 30 c4b (Z.b2z (sum4 <? s4a)).
  do 1 zstep. model_reg 17 hh1 (Z.land (c4a + p11) 18446744073709551615).
  do 1 zstep. model_reg 19 c3ab (Z.land (c3a + c3b) 18446744073709551615).
  do 1 zstep. model_reg 18 c3c (Z.b2z (sum3 <? s3b)).
  do 1 zstep. model_reg 8 r0c (Z.b2z (lo_lo <? sum1Shl32)).
  do 1 zstep. model_reg 31 sum1Mid (Z.lor sum1Shr32 c1Shl32).
  do 1 zstep. model_reg 21 sum3Shr32 (Z.shiftr sum3 32).
  do 1 zstep. model_reg 20 sum3Shl32 (Z.land (Z.shiftl sum3 32) 18446744073709551615).
  do 1 zstep. model_reg 28 c5Shl32 (Z.land (Z.shiftl c5 32) 18446744073709551615).
  do 1 zstep. model_reg 17 hh2 (Z.land (hh1 + c4b) 18446744073709551615).
  do 1 zstep. model_reg 29 m1 (Z.land (sum4 + sum2Hi) 18446744073709551615).
  do 1 zstep. model_reg 18 sum3Hi (Z.land (c3ab + c3c) 18446744073709551615).
  do 1 zstep. model_reg 31 r1a (Z.land (sum2 + sum1Mid) 18446744073709551615).
  do 1 zstep. model_reg 28 sum5MidHi (Z.lor c5Shl32 sum5Shr32).
  do 1 zstep. model_reg 13 cm1 (Z.b2z (m1 <? sum4)).
  do 1 zstep. model_reg 9 m2 (Z.land (m1 + sum5Shl32) 18446744073709551615).
  do 1 zstep. model_reg 14 cr1a (Z.b2z (r1a <? sum2)).
  do 1 zstep. model_reg 18 sum3HiShl32 (Z.land (Z.shiftl sum3Hi 32) 18446744073709551615).
  do 1 zstep. model_reg 20 r1 (Z.land (r1a + sum3Shl32) 18446744073709551615).
  do 1 zstep. model_reg 17 hh3 (Z.land (hh2 + cm1) 18446744073709551615).
  do 1 zstep. model_reg 6 cm2 (Z.b2z (m2 <? m1)).
  do 1 zstep. model_reg 29 cr1b (Z.b2z (r1 <? r1a)).
  do 1 zstep. model_reg 13 lo_hi (Z.land (r1 + r0c) 18446744073709551615).
  do 1 zstep. model_reg 30 sum3Mid (Z.lor sum3Shr32 sum3HiShl32).
  do 1 zstep. model_reg 17 hh4 (Z.land (hh3 + sum5MidHi) 18446744073709551615).
  do 1 zstep. model_reg 14 r1Hi (Z.land (cr1a + cr1b) 18446744073709551615).
  do 1 zstep. model_reg 28 carry (Z.b2z (lo_hi <? r1)).
  do 1 zstep. model_reg 17 hh5 (Z.land (hh4 + cm2) 18446744073709551615).
  do 1 zstep. model_reg 30 m3 (Z.land (m2 + sum3Mid) 18446744073709551615).
  do 1 zstep. model_reg 6 cm3 (Z.b2z (m3 <? m2)).
  do 1 zstep. model_reg 14 m4 (Z.land (m3 + r1Hi) 18446744073709551615).
  do 1 zstep. model_reg 6 hh6 (Z.land (hh5 + cm3) 18446744073709551615).
  do 1 zstep. model_reg 29 cm4 (Z.b2z (m4 <? m3)).
  do 1 zstep. model_reg 17 hi_lo (Z.land (m4 + carry) 18446744073709551615).
  do 1 zstep. model_reg 6 hh7 (Z.land (hh6 + cm4) 18446744073709551615).
  do 1 zstep. model_reg 14 cm5 (Z.b2z (hi_lo <? m4)).
  do 1 zstep. model_reg 14 hi_hi (Z.land (hh7 + cm5) 18446744073709551615).

  apply evt_done. unfold multf3_mid.
  exists expSum, hi_hi, hi_lo, lo_hi, lo_lo.
  repeat (lazymatch goal with |- ex _ => eexists end).
  split.
  { intros sg sc. cbv delta [mul_core]. sf_vocab. fold_model_lets. cbv delta [MC_tail]. sf_vocab. reflexivity. }
  split. { subst expSum aExp bExp. rewrite land_W64, Z.mod_small by lia. lia. }
  split. { exact Rhi_hi. } split. { exact Rhi_lo. } split. { exact Rlo_hi. } split. { exact Rlo_lo. }
  split. { reflexivity. } split. { reflexivity. } split. { reflexivity. } split. { reflexivity. }
  reflexivity.
Time Qed.
