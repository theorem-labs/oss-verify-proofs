(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import SFW_add_split.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sf_lib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_fe_getround F_addtf3_A.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import ImageA.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.

Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.

Ltac finL := first [ eassumption | reflexivity | zrange | lia | (decide_tests_b; reflexivity) | fail 1 "finL: unsolved premise" ].

Section Proofs.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte).
  Hypothesis FRM : frm0 fc.
  Hypothesis MI : mem_inv asegs m1.
  Hypothesis FR : rw_cells asegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk asegs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono asegs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom asegs)).

  Lemma add_L658 : forall x1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 (xHi SLo aExp shiftS d mask nhi r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= shiftS < 2^64)%Z ->
    (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
    (if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
    r = subR3 xHi SLo aExp shiftS mask nhi ->
    evt asegs (POST r) (ST 0x150254 fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 nhi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 shiftS) (Z_to_bv 64 d) x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 Hm HR. subst r. unfold subR3, shl128_lo, add_M7. unfold_sfw.
    assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. zstep. rewrite (srai63_word d), Hm by lia.
    zstep. name_reg 11%Z nlo.
    zstep. model_reg 15%Z aExp2 (Z.land (aExp - shiftS) W64).
    do 3 zstep. zstep. model_reg 18%Z signHi (Z.land (Z.shiftl (Z.shiftr xHi 63) 63) W64).
    zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_tests_b.
    -
      do 5 zstep. eapply add_Lret; finL.
    - eapply add_LM8; finL.
  Qed.

  Lemma add_L488 : forall x1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 (xHi SHi SLo aExp word hz r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
    r = subR2 xHi SHi SLo aExp word hz ->
    evt asegs (POST r) (ST 0x150084 fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 hz) (Z_to_bv 64 word) x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold subR2, clz128_w. unfold shl128_mirror. unfold_sfw.

    do 5 zstep. model_reg 17%Z x1_ (Z.lor word (Z.shiftr word 1)).
    do 5 zstep. model_reg 17%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
    do 8 zstep. model_reg 17%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
    do 2 zstep. model_reg 17%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
    do 2 zstep. model_reg 17%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
    do 2 zstep. model_reg 17%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
    zstep. model_reg 17%Z y_ (Z.lxor x6_ W64).
    do 4 zstep. model_reg 17%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
    do 6 zstep. model_reg 17%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
    do 4 zstep. model_reg 17%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
    do 3 zstep. model_reg 17%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
    name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
    zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    name_reg 16%Z clzS.
    zstep. model_reg 16%Z shiftS (Z.land (clzS - 12) W64).
    zstep. zstep. name_reg 5%Z n. zstep. model_reg 17%Z d (Z.land (n - 64) W64).
    zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
    -
      zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. name_reg 10%Z nhi.
      eapply add_L658 with (mask := 18446744073709551615%Z); finL.
    -
      zstep. model_reg 10%Z nhi (Z.land (Z.shiftl SLo (Z.land n 63)) W64). zstep.
      eapply add_L658 with (mask := 0%Z); finL.
  Qed.

  Lemma add_Lsub : forall x1 x6 x8 x9 x11 x17 x18 x19 x20 x28 x29 x30 x31 (xHi AHi ALo BHi BLo aExp r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= AHi < 2^64)%Z -> (0 <= ALo < 2^64)%Z -> (0 <= BHi < 2^64)%Z -> (0 <= BLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    r = add_M6s xHi AHi ALo BHi BLo aExp ->
    evt asegs (POST r) (ST 0x150040 fc x1 (Z_to_bv 64 ALo) x6 (Z_to_bv 64 BLo) x8 x9 (Z_to_bv 64 AHi) x11 (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 BHi) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold add_M6s, addsub_sub. unfold_sfw. rewrite ?b2z_Zb2z.
    do 4 zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
    -
      zstep. name_reg 11%Z borrow.
      zstep. zstep. model_reg 10%Z SHi (Z.land (Z.land (AHi - BHi) W64 - borrow) W64).
      zstep. zstep. model_reg 11%Z SLo (Z.land (ALo - BLo) W64).
      zstep. if_cases Kr; zify_cond Kr; decide_tests_b.
      +   eapply add_LM7; finL.
      +
        rewrite clz128_mirror_w. rewrite ?b2z_Zb2z.
        zstep. rewrite (ltb1_eqb0 SHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_tests_b.
        *   change (Z.b2z true) with 1%Z. eapply add_L488; finL.
        * change (Z.b2z false) with 0%Z. zstep. eapply add_L488; finL.
    -
      do 3 zstep. eapply add_Lret; finL.
  Qed.

  Lemma add_Ladd : forall x1 x6 x8 x9 x11 x17 x18 x19 x20 x28 x29 x30 x31 (xHi AHi ALo BHi BLo aExp r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= AHi < 2^64)%Z -> (0 <= ALo < 2^64)%Z -> (0 <= BHi < 2^64)%Z -> (0 <= BLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    r = add_M6a xHi AHi ALo BHi BLo aExp ->
    evt asegs (POST r) (ST 0x1501bc fc x1 (Z_to_bv 64 ALo) x6 (Z_to_bv 64 BLo) x8 x9 (Z_to_bv 64 AHi) x11 (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 BHi) x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 HR. subst r. unfold add_M6a, addsub_add. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. model_reg 11%Z SLo (Z.land (BLo + ALo) W64).
    zstep. name_reg 17%Z carry.
    zstep. zstep.
    replace (Z_to_bv 64 (BHi + AHi + carry)) with (Z_to_bv 64 (Z.land (Z.land (BHi + AHi) W64 + carry) W64))
      by (apply Z_to_bv_eqm; rewrite !land_W64; Z.div_mod_to_equations; lia).
    name_as SHi (Z.land (Z.land (BHi + AHi) W64 + carry) W64).
    zstep. zstep. if_cases Kc; zify_cond Kc; decide_tests_b.
    -   eapply add_LM7; finL.
    -
      zstep. name_reg 16%Z st.
      do 5 zstep. name_reg 11%Z SLo2.
      zstep. model_reg 15%Z aExp2 (Z.land (aExp + 1) W64).
      eapply add_LM7; finL.
  Qed.
End Proofs.
