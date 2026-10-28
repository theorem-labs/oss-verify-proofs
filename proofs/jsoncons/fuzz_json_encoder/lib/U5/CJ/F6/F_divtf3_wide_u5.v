(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.Lib Require Import SFModel.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_mul_core1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_sf_helpers3.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_div_wide.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import F_f128_div_core1.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_multf3_core_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_divtf3_core_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition divtf3_mid2_pc := 0xb7a24%Z.

Lemma ltb1_eqb0 : forall x, 0 <= x -> (x <? 1) = (x =? 0).
Proof. intros. destruct (Z.ltb_spec0 x 1); destruct (Z.eqb_spec x 0); try reflexivity; lia. Qed.

(* [comment removed for export] *)
Definition divtf3_mid2 (sp gp tp w4 sgw w6 a6 : word) (F : bvmap 5 word) (fc : bv 32)
    (ea eb aSigHi bSigHi scale x_hi x_lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
    divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi (bv_unsigned w4)) (E_A3 (bv_unsigned w4)) (E_A4 (bv_unsigned w4)) = (q_hi, q_lo)
    /\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
    /\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
                 y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                 (Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
             F (Z_to_bv 64 0xb7a24) fc None m (seg_rom rsegs).

Section Core2.
  Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
  Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
  Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

  Lemma divtf3_core2 : forall (x_hi x_lo : Z) (ra sp gp tp sgw a5 a6 y21 y22 s10 s11 : word)
      (F : bvmap 5 word) fc (m : word -> option byte),
    mem_inv rsegs m ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    (0 <= x_hi < 2^64)%Z -> (0 <= x_lo < 2^64)%Z ->
    evt rsegs (divtf3_mid2 sp gp tp w4 sgw w6 a6 F fc ea eb aSigHi bSigHi scale x_hi x_lo m)
      (MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
                 (Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
                 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                 (Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
                 (Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
                 (Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
          F (Z_to_bv 64 0xb78e4) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI Ra Rb Rsc Rx_hi Rx_lo.
    pose_word_ranges.
    (* [comment removed for export] *)
    cbv beta delta [E_p3 E_p42 E_X4 E_X4sh E_X3 E_A2sh E_A1 E_A2 E_A3 E_A4 E_aLoTop E_aHi2n E_aHi2 E_aSigHiI E_bSigHiI E_a2Lo E_expM1].
    name_as aSigHiI (Z.lor aSigHi 281474976710656). name_as bSigHiI (Z.lor bSigHi 281474976710656).
    name_as aLoTop (Z.shiftr aLo 63). name_as a2Lo (Z.land (Z.shiftl aLo 1) 18446744073709551615).
    name_as aHi2n (Z.land (Z.shiftl aSigHi 1) 18446744073709551615). name_as aHi2 (Z.land (Z.shiftl aSigHiI 1) 18446744073709551615).
    name_as A1 (Z.shiftr aHi2 32). name_as A2 (Z.land (Z.lor aLoTop aHi2n) 4294967295).
    name_as A3 (Z.shiftr a2Lo 32). name_as A4 (Z.land a2Lo 4294967294).
    name_as X3 (Z.shiftr x_lo 32). name_as X4sh (Z.land (Z.shiftl x_lo 32) 18446744073709551615). name_as X4 (Z.shiftr X4sh 32).
    name_as p31 (Z.land (X3 * A1) 18446744073709551615). name_as p32 (Z.land (X3 * A2) 18446744073709551615).
    name_as p33 (Z.land (X3 * A3) 18446744073709551615). name_as p34 (Z.land (X3 * A4) 18446744073709551615).
    name_as p42 (Z.land (X4 * A2) 18446744073709551615).
    (* [comment removed for export] *)
    do 1 zstep. model_reg 22 p41 (Z.land (X4 * A1) 18446744073709551615).
    do 1 zstep. model_reg 26 p43 (Z.land (X4 * A3) 18446744073709551615).
    do 1 zstep. model_reg 27 p44 (Z.land (X4 * A4) 18446744073709551615).
    do 1 zstep. model_reg 21 s2a (Z.land (p42 + p33) 18446744073709551615).
    do 1 zstep. model_reg 23 X1 (Z.shiftr x_hi 32).
    do 1 zstep. model_reg 25 X2sh (Z.land (Z.shiftl x_hi 32) 18446744073709551615).
    do 1 zstep. model_reg 26 sum1 (Z.land (p34 + p43) 18446744073709551615).
    do 1 zstep. model_reg 19 c2a (Z.b2z (s2a <? p42)).
    do 1 zstep. model_reg 20 p11 (Z.land (X1 * A1) 18446744073709551615).
    do 1 zstep. model_reg 18 p12 (Z.land (A2 * X1) 18446744073709551615).
    do 1 zstep. model_reg 1 p13 (Z.land (A3 * X1) 18446744073709551615).
    do 1 zstep. model_reg 23 p14 (Z.land (A4 * X1) 18446744073709551615).
    do 1 zstep. model_reg 15 X2 (Z.shiftr X2sh 32).
    do 1 zstep. cbv delta [X2sh]. rewrite mulhu_shl32 by zrange_nonneg. replace (Z.land x_hi 4294967295) with X2 by (cbv delta [X2 X2sh]; apply shl_shr_32; zrange_nonneg). change (Z.land (Z.lor aLoTop aHi2n) 4294967295) with A2. change (Z.land (Z.shiftl x_hi 32) 18446744073709551615) with X2sh.
    do 0 zstep. model_reg 9 p22 (Z.land (X2 * A2) 18446744073709551615).
    do 1 zstep. model_reg 24 c1 (Z.b2z (sum1 <? p34)).
    do 1 zstep. model_reg 25 sum1Shr32 (Z.shiftr sum1 32).
    do 1 zstep. model_reg 26 sum1Shl32 (Z.land (Z.shiftl sum1 32) 18446744073709551615).
    do 1 zstep. model_reg 8 p21 (Z.land (X2 * A1) 18446744073709551615).
    do 1 zstep. model_reg 31 p23 (Z.land (X2 * A3) 18446744073709551615).
    do 1 zstep. model_reg 15 p24 (Z.land (X2 * A4) 18446744073709551615).
    do 1 zstep. model_reg 23 s3a (Z.land (p41 + p14) 18446744073709551615).
    do 1 zstep. model_reg 24 c1Shl32 (Z.land (Z.shiftl c1 32) 18446744073709551615).
    do 1 zstep. model_reg 27 lo_lo (Z.land (sum1Shl32 + p44) 18446744073709551615).
    do 1 zstep. model_reg 1 s4a (Z.land (p31 + p13) 18446744073709551615).
    do 1 zstep. model_reg 15 sum2 (Z.land (s2a + p24) 18446744073709551615).
    do 1 zstep. model_reg 28 c3a (Z.b2z (s3a <? p41)).
    do 1 zstep. model_reg 30 s3b (Z.land (s3a + p32) 18446744073709551615).
    do 1 zstep. model_reg 18 sum5 (Z.land (p21 + p12) 18446744073709551615).
    do 1 zstep. model_reg 22 r0c (Z.b2z (lo_lo <? sum1Shl32)).
    do 1 zstep. model_reg 24 sum1Mid (Z.lor sum1Shr32 c1Shl32).
    do 1 zstep. model_reg 29 c4a (Z.b2z (s4a <? p31)).
    do 1 zstep. model_reg 9 sum4 (Z.land (s4a + p22) 18446744073709551615).
    do 1 zstep. model_reg 21 c2b (Z.b2z (sum2 <? s2a)).
    do 1 zstep. model_reg 23 c3b (Z.b2z (s3b <? s3a)).
    do 1 zstep. model_reg 31 sum3 (Z.land (s3b + p23) 18446744073709551615).
    do 1 zstep. model_reg 8 c5 (Z.b2z (sum5 <? p21)).
    do 1 zstep. model_reg 24 r1a (Z.land (sum2 + sum1Mid) 18446744073709551615).
    do 1 zstep. model_reg 22 nr0c (Z.lxor r0c 18446744073709551615).
    do 1 zstep. model_reg 25 sum5Shr32 (Z.shiftr sum5 32).
    do 1 zstep. model_reg 18 sum5Shl32 (Z.land (Z.shiftl sum5 32) 18446744073709551615).
    do 1 zstep. model_reg 26 c4b (Z.b2z (sum4 <? s4a)).
    do 1 zstep. model_reg 29 hh1 (Z.land (c4a + p11) 18446744073709551615).
    do 1 zstep. model_reg 19 sum2Hi (Z.land (c2a + c2b) 18446744073709551615).
    do 1 zstep. model_reg 28 c3ab (Z.land (c3a + c3b) 18446744073709551615).
    do 1 zstep. model_reg 30 c3c (Z.b2z (sum3 <? s3b)).
    do 1 zstep. model_reg 15 cr1a (Z.b2z (r1a <? sum2)).
    do 1 zstep. model_reg 20 sum3Shr32 (Z.shiftr sum3 32).
    do 1 zstep. model_reg 31 sum3Shl32 (Z.land (Z.shiftl sum3 32) 18446744073709551615).
    do 1 zstep. model_reg 8 c5Shl32 (Z.land (Z.shiftl c5 32) 18446744073709551615).
    do 1 zstep. model_reg 29 hh2 (Z.land (hh1 + c4b) 18446744073709551615).
    do 1 zstep. model_reg 18 m1 (Z.land (sum4 + sum5Shl32) 18446744073709551615).
    do 1 zstep. model_reg 28 sum3Hi (Z.land (c3ab + c3c) 18446744073709551615).
    do 1 zstep. model_reg 31 r1 (Z.land (r1a + sum3Shl32) 18446744073709551615).
    do 1 zstep. model_reg 30 sum5MidHi (Z.lor c5Shl32 sum5Shr32).
    do 1 zstep. model_reg 8 cm1 (Z.b2z (m1 <? sum4)).
    do 1 zstep. model_reg 19 m2 (Z.land (m1 + sum2Hi) 18446744073709551615).
    do 1 zstep. model_reg 28 sum3HiShl32 (Z.land (Z.shiftl sum3Hi 32) 18446744073709551615).
    do 1 zstep. model_reg 9 cr1b (Z.b2z (r1 <? r1a)).
    do 1 zstep. model_reg 21 ltc (Z.b2z (nr0c <? r1)).
    do 1 zstep. model_reg 31 eqx (Z.lxor r1 nr0c).
    do 1 zstep. model_reg 29 hh3 (Z.land (hh2 + sum5MidHi) 18446744073709551615).
    do 1 zstep. model_reg 30 cm2 (Z.b2z (m2 <? m1)).
    do 1 zstep. model_reg 15 r1Hi (Z.land (cr1a + cr1b) 18446744073709551615).
    do 2 zstep. model_reg 28 sum3Mid (Z.lor sum3Shr32 sum3HiShl32).
    do 1 zstep. model_reg 29 hh4 (Z.land (hh3 + cm1) 18446744073709551615).
    zstep.
    replace (Z_to_bv 64 (Z.b2z (eqx <? 1) + -1)) with (Z_to_bv 64 (Z.land (Z.b2z (eqx =? 0) - 1) 18446744073709551615))
      by (rewrite Z_to_bv_land64, ltb1_eqb0 by lia; f_equal; lia).
    model_reg 31 neMask (Z.land (Z.b2z (eqx =? 0) - 1) 18446744073709551615).
    zstep. model_reg 29 hh5 (Z.land (hh4 + cm2) 18446744073709551615).
    do 1 zstep. model_reg 28 m3 (Z.land (m2 + sum3Mid) 18446744073709551615).
    zstep. model_reg 30 carry (Z.land neMask ltc).
    zstep. model_reg 31 cm3 (Z.b2z (m3 <? m2)).
    do 1 zstep. model_reg 15 m4 (Z.land (m3 + r1Hi) 18446744073709551615).
    do 1 zstep. model_reg 29 hh6 (Z.land (hh5 + cm3) 18446744073709551615).
    do 1 zstep. model_reg 28 cm4 (Z.b2z (m4 <? m3)).
    zstep. model_reg 30 q_lo (Z.land (m4 + carry) 18446744073709551615).
    zstep. model_reg 28 hh7 (Z.land (hh6 + cm4) 18446744073709551615).
    zstep. model_reg 15 cm5 (Z.b2z (q_lo <? m4)).
    zstep. model_reg 28 q_hi (Z.land (hh7 + cm5) 18446744073709551615).
    do 2 zstep.
    apply evt_done. unfold divtf3_mid2.
    exists q_hi, q_lo. repeat (lazymatch goal with |- ex _ => eexists end).
    split.
    { change (divc_wide x_hi x_lo A1 A2 A3 A4 = (q_hi, q_lo)).
      cbv beta delta [divc_wide]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
    split. { exact Rq_hi. } split. { exact Rq_lo. }
    reflexivity.
  Time Qed.

  (* [comment removed for export] *)
  Definition divtf3_midC (sp gp tp sgw a6 : word) (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) : machine_state -> Prop :=
    fun ms' => exists q_hi q_lo y1 y8 y9 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y31,
      (forall sgn, div_core sgn ea eb aSigHi aLo bSigHi bLo scale
                   = divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo))
      /\ (0 <= q_hi < 2^64)%Z /\ (0 <= q_lo < 2^64)%Z
      /\ ms' = MS (mkR y1 sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop aLo)) (Z_to_bv 64 (E_aHi2 aSigHi))
                   y8 y9 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo aLo)) (Z_to_bv 64 (Z.shiftr q_hi 49)) a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                   y18 y19 y20 y21 y22 y23 y24 y25 y26 y27
                   (Z_to_bv 64 q_hi) (Z_to_bv 64 (E_expM1 scale ea eb + 1)) (Z_to_bv 64 q_lo) y31)
               F (Z_to_bv 64 0xb7a24) fc None m (seg_rom rsegs).

  Lemma divtf3_core12 : forall (ra sp gp tp s0 s1 sgw a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
      (F : bvmap 5 word) fc (m : word -> option byte),
    mem_inv rsegs m ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    evt rsegs (divtf3_midC sp gp tp sgw a6 F fc m)
      (MS (mkR ra sp gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) s0 s1 w4 sgw w6 a3 a4 a5 a6 w3
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 0xb7754) fc None m (seg_rom rsegs)).
  Proof.
    intros until m. intros MI Ra Rb Rsc.
    eapply evt_cut. { eapply divtf3_core1; eauto. }
    intros ms1 P. destruct P as (xh' & xl' & y21 & y22 & EQ1 & Rxh & Rxl & ->).
    eapply evt_mono. { eapply divtf3_core2; eauto. }
    intros ms2 P2. destruct P2 as (q_hi & q_lo & y1 & y8 & y9 & y18 & y19 & y20 & z21 & z22 & y23 & y24 & y25 & y26 & y27 & y31 & HW & Rqh & Rql & ->).
    unfold divtf3_midC. exists q_hi, q_lo. repeat (lazymatch goal with |- ex _ => eexists end).
    split. { intros sgn. rewrite EQ1. cbv beta delta [DCW]. rewrite HW. reflexivity. }
    split. { exact Rqh. } split. { exact Rql. }
    reflexivity.
  Qed.
End Core2.
