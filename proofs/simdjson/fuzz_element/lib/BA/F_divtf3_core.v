(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import F_f128_mul_core1 F_sf_helpers3 F_f128_div_wide F_f128_div_core1.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_multf3_core F_divtf3.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import ImageA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Definition divtf3_core_pc := 0x1505bc%Z.
Definition divtf3_mid1_pc := 0x15074c%Z.

Lemma shl_shr_32 : forall x, 0 <= x -> Z.shiftr (Z.land (Z.shiftl x 32) 18446744073709551615) 32 = Z.land x 4294967295.
Proof. intros. rewrite zb_shl_shr_land by lia. reflexivity. Qed.

Definition E_aSigHiI (aSigHi : Z) := Z.lor aSigHi 281474976710656.
Definition E_bSigHiI (bSigHi : Z) := Z.lor bSigHi 281474976710656.
Definition E_aLoTop (aLo : Z) := Z.shiftr aLo 63.
Definition E_a2Lo (aLo : Z) := Z.land (Z.shiftl aLo 1) 18446744073709551615.
Definition E_aHi2n (aSigHi : Z) := Z.land (Z.shiftl aSigHi 1) 18446744073709551615.
Definition E_aHi2 (aSigHi : Z) := Z.land (Z.shiftl (E_aSigHiI aSigHi) 1) 18446744073709551615.
Definition E_A1 (aSigHi : Z) := Z.shiftr (E_aHi2 aSigHi) 32.
Definition E_A2 (aSigHi aLo : Z) := Z.land (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 4294967295.
Definition E_A2sh (aSigHi aLo : Z) := Z.shiftl (Z.lor (E_aLoTop aLo) (E_aHi2n aSigHi)) 32.
Definition E_A3 (aLo : Z) := Z.shiftr (E_a2Lo aLo) 32.
Definition E_A4 (aLo : Z) := Z.land (E_a2Lo aLo) 4294967294.
Definition E_X3 (x_lo : Z) := Z.shiftr x_lo 32.
Definition E_X4sh (x_lo : Z) := Z.land (Z.shiftl x_lo 32) 18446744073709551615.
Definition E_X4 (x_lo : Z) := Z.shiftr (E_X4sh x_lo) 32.
Definition E_p3 (x_lo A : Z) := Z.land (E_X3 x_lo * A) 18446744073709551615.
Definition E_p42 (x_lo aSigHi aLo : Z) := Z.land (E_X4 x_lo * E_A2 aSigHi aLo) 18446744073709551615.
Definition E_expM1 (scale ea eb : Z) := scale + 16382 + (ea - eb).
Definition E_blo (bLo : Z) := Z.land (Z.shiftl bLo 15) 18446744073709551615.
Definition E_bhw (bSigHi bLo : Z) := Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl (E_bSigHiI bSigHi) 15) 18446744073709551615).
Definition E_x0 (bSigHi bLo : Z) := Z.land (8432131802713292800 - E_bhw bSigHi bLo) 18446744073709551615.

Definition DCW (sgn ea eb aSigHi aLo bSigHi bLo scale x_hi x_lo : Z) : Z :=
  let '(q_hi, q_lo) := divc_wide x_hi x_lo (E_A1 aSigHi) (E_A2 aSigHi aLo) (E_A3 aLo) (E_A4 aLo) in
  divc_tail sgn (E_expM1 scale ea eb) q_hi q_lo aLo (E_aSigHiI aSigHi) (E_bSigHiI bSigHi) bLo (E_aHi2 aSigHi) (E_aLoTop aLo) (E_a2Lo aLo).

Ltac half_block b_hw xp xn h corr lo hi r :=
  zstep; model_reg 22 h (Z.shiftr (xp * b_hw) 64); mulhu_rng h;
  zstep; model_reg 22 corr (Z.land (0 - h) 18446744073709551615);
  zstep; model_reg 23 lo (Z.land (corr * xp) 18446744073709551615);
  zstep; model_reg 21 hi (Z.shiftr (corr * xp) 64); mulhu_rng hi;
  do 3 zstep; model_reg 21 r (Z.lor (Z.shiftr lo 63) (Z.land (Z.shiftl hi 1) 18446744073709551615));
  replace (Z_to_bv 64 r) with (Z_to_bv 64 (half_iter xp b_hw)) by (f_equal; subst r hi lo corr h; reflexivity);
  name_as xn (half_iter xp b_hw); hi_rng xn.

Definition divtf3_mid1 (ra sp gp tp w4 sgw w6 a5 a6 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (ea eb aSigHi bSigHi scale : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x_hi x_lo y21 y22,
    (forall sgn, div_core sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale
                 = DCW sgn ea eb aSigHi (bv_unsigned w4) bSigHi (bv_unsigned w6) scale x_hi x_lo)
    /\ (0 <= x_hi < 2^64)%Z /\ (0 <= x_lo < 2^64)%Z
    /\ ms' = MS (mkR ra sp gp tp (Z_to_bv 64 (E_expM1 scale ea eb)) (Z_to_bv 64 (E_aLoTop (bv_unsigned w4))) (Z_to_bv 64 (E_aHi2 aSigHi))
                 (Z_to_bv 64 (E_A1 aSigHi)) (Z_to_bv 64 (E_A2sh aSigHi (bv_unsigned w4)))
                 w4 sgw w6 (Z_to_bv 64 (E_bSigHiI bSigHi)) (Z_to_bv 64 (E_a2Lo (bv_unsigned w4))) a5 a6 (Z_to_bv 64 (E_aSigHiI aSigHi))
                 (Z_to_bv 64 (E_A2 aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_p42 x_lo aSigHi (bv_unsigned w4))) (Z_to_bv 64 (E_X4 x_lo)) y21 y22
                 (Z_to_bv 64 (E_p3 x_lo (E_A3 (bv_unsigned w4)))) (Z_to_bv 64 (E_p3 x_lo (E_A4 (bv_unsigned w4)))) (Z_to_bv 64 x_hi) s10 s11
                 (Z_to_bv 64 (E_A4 (bv_unsigned w4))) (Z_to_bv 64 (E_p3 x_lo (E_A1 aSigHi))) (Z_to_bv 64 (E_p3 x_lo (E_A2 aSigHi (bv_unsigned w4)))) (Z_to_bv 64 (E_A3 (bv_unsigned w4))))
             F (Z_to_bv 64 0x15074c) fc None m (seg_rom asegs).

Section Core1.
  Variables (w3 w4 w5 w6 : word) (ea eb scale : Z).
  Notation aSigHi := (bv_unsigned w3). Notation aLo := (bv_unsigned w4).
  Notation bSigHi := (bv_unsigned w5). Notation bLo := (bv_unsigned w6).

  Lemma divtf3_core1 : forall (ra sp gp tp s0 s1 sgw a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word)
      (F : bvmap 5 word) fc (m : word -> option byte),
    mem_inv asegs m ->
    (0 <= ea < 32768)%Z -> (0 <= eb < 32768)%Z -> (-1024 <= scale <= 1024)%Z ->
    evt asegs (divtf3_mid1 ra sp gp tp w4 sgw w6 a5 a6 s10 s11 F fc ea eb aSigHi bSigHi scale m)
      (MS (mkR ra sp gp tp w5 (Z_to_bv 64 ea) (Z_to_bv 64 eb) s0 s1 w4 sgw w6 a3 a4 a5 a6 w3
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 scale) t4 t5 t6)
          F (Z_to_bv 64 0x1505bc) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI Ra Rb Rsc.
    pose_word_ranges.
    set (aExp := ea) in *. set (bExp := eb) in *.

    do 3 zstep. model_reg 7 expDiff (aExp - bExp).
    do 1 zstep. model_reg 30 blo (Z.land (Z.shiftl bLo 15) 18446744073709551615).
    do 4 zstep. model_reg 6 aLoTop (Z.shiftr aLo 63).
    do 1 zstep. model_reg 14 a2Lo (Z.land (Z.shiftl aLo 1) 18446744073709551615).
    do 1 zstep. model_reg 18 aHi2n (Z.land (Z.shiftl aSigHi 1) 18446744073709551615).
    do 7 zstep. model_reg 31 A3 (Z.shiftr a2Lo 32).
    do 2 zstep. model_reg 17 aSigHiI (Z.lor aSigHi 281474976710656).
    do 1 zstep. model_reg 13 bSigHiI (Z.lor bSigHi 281474976710656).
    do 5 zstep. model_reg 5 expM1 ((scale + 16382) + expDiff).
    do 2 zstep. model_reg 7 aHi2 (Z.land (Z.shiftl aSigHiI 1) 18446744073709551615).
    do 1 zstep. model_reg 18 A2 (Z.land (Z.lor aLoTop aHi2n) 4294967295).
    do 1 zstep. model_reg 28 A4 (Z.land a2Lo 4294967294).
    do 1 zstep. model_reg 20 b_hw (Z.lor (Z.shiftr bLo 49) (Z.land (Z.shiftl bSigHiI 15) 18446744073709551615)).
    do 1 zstep. model_reg 8 A1 (Z.shiftr aHi2 32).
    do 1 zstep. model_reg 21 x0 (Z.land (8432131802713292800 - b_hw) 18446744073709551615).

    half_block b_hw x0 hx1 h1 k1 lo1 hi1 r1.
    half_block b_hw hx1 hx2 h2 k2 lo2 hi2 r2.
    half_block b_hw hx2 hx3 h3 k3 lo3 hi3 r3.
    half_block b_hw hx3 hx4 h4 k4 lo4 hi4 r4.
    do 1 zstep. model_reg 21 xh (Z.land (hx4 - 1) 18446744073709551615).
    do 1 zstep. model_reg 22 pHhi (Z.shiftr (b_hw * xh) 64). mulhu_rng pHhi.
    do 1 zstep. model_reg 20 pHlo (Z.land (b_hw * xh) 18446744073709551615).
    do 1 zstep. model_reg 30 pLhi (Z.shiftr (blo * xh) 64). mulhu_rng pLhi.
    do 1 zstep. model_reg 30 sumlo (Z.land (pHlo + pLhi) 18446744073709551615).
    do 1 zstep. model_reg 20 c0 (Z.b2z (sumlo <? pHlo)).
    do 1 zstep. model_reg 23 lt2 (Z.b2z (sumlo <? 2)).
    do 1 zstep. model_reg 29 lo_corr (Z.land (1 - sumlo) 18446744073709551615).
    do 1 zstep. model_reg 20 hiP (Z.land (pHhi + c0) 18446744073709551615).
    do 1 zstep. model_reg 30 ge2 (Z.lxor lt2 1).
    do 1 zstep. model_reg 22 m1lo (Z.land (lo_corr * xh) 18446744073709551615).
    do 1 zstep. model_reg 29 m1hi (Z.shiftr (lo_corr * xh) 64). mulhu_rng m1hi.
    do 1 zstep. model_reg 30 negHi (Z.land (hiP + ge2) 18446744073709551615).
    do 3 zstep. model_reg 29 Bhi (Z.shiftr m1hi 63).
    do 1 zstep. model_reg 30 hi_corr (Z.land (0 - negHi) 18446744073709551615).
    do 1 zstep. model_reg 20 Blo (Z.lor (Z.shiftr m1lo 63) (Z.land (Z.shiftl m1hi 1) 18446744073709551615)).
    do 1 zstep. model_reg 22 m2lo (Z.land (xh * hi_corr) 18446744073709551615).
    do 1 zstep. model_reg 30 m2hi (Z.shiftr (xh * hi_corr) 64). mulhu_rng m2hi.
    do 3 zstep. model_reg 22 Alo (Z.land (Z.shiftl m2lo 1) 18446744073709551615).
    do 1 zstep. model_reg 30 Ahi (Z.lor (Z.land (Z.shiftl m2hi 1) 18446744073709551615) (Z.shiftr m2lo 63)).
    do 1 zstep. model_reg 20 sLo (Z.land (Alo + Blo) 18446744073709551615).
    do 1 zstep. model_reg 29 sHi (Z.land (Ahi + Bhi) 18446744073709551615).
    do 1 zstep. model_reg 30 cs1 (Z.b2z (sLo <? Alo)).
    do 1 zstep. model_reg 19 x_lo (Z.land (sLo + 18446744073709537689) 18446744073709551615).
    do 1 zstep. model_reg 29 sHi1 (Z.land (sHi + cs1) 18446744073709551615).
    do 1 zstep. model_reg 30 cs2 (Z.b2z (x_lo <? sLo)).
    do 1 zstep. model_reg 20 X3 (Z.shiftr x_lo 32).
    do 1 zstep. model_reg 19 X4sh (Z.land (Z.shiftl x_lo 32) 18446744073709551615).
    do 1 zstep. model_reg 21 sHi2 (Z.land (sHi1 + cs2) 18446744073709551615).
    do 1 zstep. model_reg 29 p31 (Z.land (X3 * A1) 18446744073709551615).
    do 1 zstep. model_reg 30 p32 (Z.land (X3 * A2) 18446744073709551615).
    do 1 zstep. model_reg 23 p33 (Z.land (X3 * A3) 18446744073709551615).
    do 1 zstep. model_reg 24 p34 (Z.land (X3 * A4) 18446744073709551615).
    do 1 zstep. model_reg 20 X4 (Z.shiftr X4sh 32).
    do 1 zstep. cbv delta [X4sh]. rewrite mulhu_shl32 by zrange_nonneg. replace (Z.land x_lo 4294967295) with X4 by (cbv delta [X4 X4sh]; apply shl_shr_32; zrange_nonneg). change (Z.land (Z.lor aLoTop aHi2n) 4294967295) with A2. change (Z.land (Z.shiftl x_lo 32) 18446744073709551615) with X4sh.
    do 0 zstep. model_reg 19 p42 (Z.land (X4 * A2) 18446744073709551615).
    do 1 zstep. model_reg 25 x_hi (Z.land (sHi2 - 1) 18446744073709551615).

    apply evt_done. unfold divtf3_mid1.
    exists x_hi, x_lo. eexists. eexists.
    split.
    { intros sg. cbv beta delta [DCW].
      change (E_A1 aSigHi) with A1. change (E_A2 aSigHi aLo) with A2. change (E_A3 aLo) with A3. change (E_A4 aLo) with A4.
      change (E_expM1 scale aExp bExp) with expM1. change (E_aSigHiI aSigHi) with aSigHiI. change (E_bSigHiI bSigHi) with bSigHiI.
      change (E_aHi2 aSigHi) with aHi2. change (E_aLoTop aLo) with aLoTop. change (E_a2Lo aLo) with a2Lo.
      cbv beta delta [div_core].
      change (divc_setup aExp bExp aSigHi aLo bSigHi bLo scale) with (expM1, blo, b_hw, A1, A2, A3, A4, aSigHiI, bSigHiI, aHi2, aLoTop, a2Lo, x0).
      cbv beta iota.
      assert (HN : divc_newton x0 b_hw = xh).
      { cbv delta [divc_newton]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
      rewrite HN. cbv beta iota zeta.
      assert (HF : divc_full xh b_hw blo = (x_hi, x_lo)).
      { cbv delta [divc_full]. sf_vocab. fold_model_lets. folded_check. reflexivity. }
      rewrite HF. cbv beta iota. reflexivity. }
    split. { exact Rx_hi. } split. { exact Rx_lo. }
    reflexivity.
  Time Qed.
End Core1.
