(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SFW_add_split.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_fe_getround_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_addtf3_A_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_addtf3_B_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_addtf3_C_u.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.FA Require Import SF_buildtac.
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
  Hypothesis MI : mem_inv rsegs m1.
  Hypothesis FR : rw_cells rsegs m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis STK : stk rsegs m1 (bv_unsigned sp + -48) (bv_unsigned sp + -48).
  Hypothesis MU : munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m1.
  Hypothesis WM : wmono rsegs m m1.
  Hypothesis SPLO : (48 <= bv_unsigned sp)%Z.

  Notation POST r := (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F r m).
  Notation SP := (Z_to_bv 64 (bv_unsigned sp + -48)).

  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom rsegs)).

  Lemma add_L3ac : forall x1 x9 x18 x19 x20 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh d mask nhi r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigLo < 2^64)%Z -> (0 <= clz < 2^64)%Z -> (0 <= sh < 2^64)%Z -> (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
    (if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
    r = normB3 aHi bHi xHi aSigHi aSigLo aExp bSigLo clz sh mask nhi ->
    evt rsegs (POST r) (ST 0xb087c fc x1 (Z_to_bv 64 clz) (Z_to_bv 64 nhi) (Z_to_bv 64 sh) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 (Z_to_bv 64 d) x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold normB3, shl128_lo. unfold_sfw.
    assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. zstep. rewrite (srai63_word d), Hm by lia.
    zstep. zstep. name_reg 16%Z nlo.
    zstep. model_reg 5%Z bExp2 (Z.land (16 - clz) W64).
    eapply add_LM4; finL.
  Qed.

  Lemma add_L2d0 : forall x1 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo word hz r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z -> (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
    r = (let '(h, l, e) := norm_w2 bSigHi bSigLo word hz in add_M4 aHi bHi xHi aSigHi aSigLo aExp h l e) ->
    evt rsegs (POST r) (ST 0xb07a0 fc x1 (Z_to_bv 64 hz) (Z_to_bv 64 bSigHi) (Z_to_bv 64 word) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 HR. subst r. unfold norm_w2, clz128_w. unfold shl128_mirror. unfold_sfw.

    do 5 zstep. model_reg 7%Z x1_ (Z.lor word (Z.shiftr word 1)).
    do 5 zstep. model_reg 7%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
    do 8 zstep. model_reg 7%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
    do 2 zstep. model_reg 7%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
    do 2 zstep. model_reg 7%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
    do 2 zstep. model_reg 7%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
    zstep. model_reg 7%Z y_ (Z.lxor x6_ W64).
    do 4 zstep. model_reg 7%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
    do 6 zstep. model_reg 7%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
    do 4 zstep. model_reg 7%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
    do 3 zstep. model_reg 7%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
    name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
    zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    name_as_by clz (Z.lor clz64v (Z.shiftl hz 6))
      (change (inr64 (Z.lor clz64v (Z.shiftl hz 6))); apply zr_lor; [zrange | apply zr_lit; rewrite Z.shiftl_mul_pow2 by lia; lia]).
    zstep. model_reg 7%Z sh (Z.land (clz - 15) W64).
    zstep. zstep. name_reg 29%Z n. zstep. model_reg 28%Z d (Z.land (n - 64) W64).
    zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
    -
      zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr bSigLo 1) (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr (Z.shiftr bSigLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. name_reg 6%Z nhi.
      eapply add_L3ac with (mask := 18446744073709551615%Z); finL.
    - zstep. model_reg 6%Z nhi (Z.land (Z.shiftl bSigLo (Z.land n 63)) W64). zstep.
      eapply add_L3ac with (mask := 0%Z); finL.
  Qed.

  Lemma add_L2c0 : forall x1 x5 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z ->
    r = (let '(h, l, e) := normalize_mirror bSigHi bSigLo in add_M4 aHi bHi xHi aSigHi aSigLo aExp h l e) ->
    evt rsegs (POST r) (ST 0xb0790 fc x1 x5 (Z_to_bv 64 bSigHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 HR. subst r. rewrite normalize_mirror_w. rewrite ?b2z_Zb2z.
    zstep. rewrite (ltb1_eqb0 bSigHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_tests_b.
    -   change (Z.b2z true) with 1%Z. eapply add_L2d0; finL.
    - change (Z.b2z false) with 0%Z. zstep. eapply add_L2d0; finL.
  Qed.

  Lemma add_L2a4 : forall x1 x9 x18 x19 x20 x29 x30 x31 (aHi bHi xHi aSigLo yHi yLo bExp clz sh d mask nhi r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z ->
    (0 <= bExp < 2^64)%Z -> (0 <= clz < 2^64)%Z -> (0 <= sh < 2^64)%Z -> (0 <= d < 2^64)%Z -> (0 <= nhi < 2^64)%Z ->
    (if 9223372036854775808 <=? d then 18446744073709551615 else 0)%Z = mask ->
    r = normA3 aHi bHi xHi aSigLo yHi yLo bExp clz sh mask nhi ->
    evt rsegs (POST r) (ST 0xb0774 fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) (Z_to_bv 64 sh) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 clz) (Z_to_bv 64 yLo) (Z_to_bv 64 nhi)
                           x18 x19 x20 (Z_to_bv 64 d) x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold normA3, shl128_lo.
    assert (Rm : (0 <= mask < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    unfold add_M3b. unfold_sfw.
    zstep. zstep. rewrite (srai63_word d), Hm by lia.
    zstep. zstep. name_reg 10%Z nlo.
    zstep. model_reg 15%Z aExp2 (Z.land (16 - clz) W64).
    zstep. name_reg 6%Z bSigHi.
    zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
    -   eapply add_LM4; finL.
    -   eapply add_L2c0; finL.
  Qed.

  Lemma add_L194 : forall x1 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo yHi yLo bExp word hz r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
    (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z -> (0 <= word < 2^64)%Z -> (0 <= hz <= 1)%Z ->
    r = (let '(h, l, e) := norm_w2 aSigHi aSigLo word hz in add_M3b aHi bHi xHi h l e (Z.land yHi MASK48) yLo bExp) ->
    evt rsegs (POST r) (ST 0xb0664 fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) (Z_to_bv 64 word) (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 hz) (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 HR. subst r. unfold norm_w2, clz128_w. unfold shl128_mirror. unfold_sfw.

    do 5 zstep. model_reg 7%Z x1_ (Z.lor word (Z.shiftr word 1)).
    do 5 zstep. model_reg 7%Z x2_ (Z.lor x1_ (Z.shiftr x1_ 2)).
    do 8 zstep. model_reg 7%Z x3_ (Z.lor x2_ (Z.shiftr x2_ 4)).
    do 2 zstep. model_reg 7%Z x4_ (Z.lor x3_ (Z.shiftr x3_ 8)).
    do 2 zstep. model_reg 7%Z x5_ (Z.lor x4_ (Z.shiftr x4_ 16)).
    do 2 zstep. model_reg 7%Z x6_ (Z.lor x5_ (Z.shiftr x5_ 32)).
    zstep. model_reg 7%Z y_ (Z.lxor x6_ W64).
    do 4 zstep. model_reg 7%Z c1_ (Z.land (y_ - Z.land (Z.shiftr y_ 1) 6148914691236517205) W64).
    do 6 zstep. model_reg 7%Z c2_ (Z.land (Z.land c1_ 3689348814741910323 + Z.land (Z.shiftr c1_ 2) 3689348814741910323) W64).
    do 4 zstep. model_reg 7%Z c3_ (Z.land (Z.land (c2_ + Z.shiftr c2_ 4) W64) 1085102592571150095).
    do 3 zstep. model_reg 7%Z c4_ (Z.shiftr (Z.land (c3_ * 72340172838076673) W64) 56).
    replace (Z_to_bv 64 c4_) with (Z_to_bv 64 (clz64_mirror word)) by (f_equal; model_eval; reflexivity).
    name_as_by clz64v (clz64_mirror word) (apply clz64_mirror_range).
    zstep. rewrite (land_W64_small (Z.shiftl hz 6)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    name_as_by clz (Z.lor clz64v (Z.shiftl hz 6))
      (change (inr64 (Z.lor clz64v (Z.shiftl hz 6))); apply zr_lor; [zrange | apply zr_lit; rewrite Z.shiftl_mul_pow2 by lia; lia]).
    zstep. model_reg 7%Z sh (Z.land (clz - 15) W64).
    zstep. zstep. name_reg 29%Z n. zstep. model_reg 28%Z d (Z.land (n - 64) W64).
    zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
    -
      zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr aSigLo 1) (Z.land (Z.lxor n W64) 63))
        (change (inr64 (Z.shiftr (Z.shiftr aSigLo 1) (Z.land (Z.lxor n W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. name_reg 17%Z nhi.
      eapply add_L2a4 with (mask := 18446744073709551615%Z); finL.
    - zstep. model_reg 17%Z nhi (Z.land (Z.shiftl aSigLo (Z.land n 63)) W64). zstep.
      eapply add_L2a4 with (mask := 0%Z); finL.
  Qed.

  Lemma add_L184 : forall x1 x7 x9 x15 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo yHi yLo bExp r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
    (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
    r = (let '(h, l, e) := normalize_mirror aSigHi aSigLo in add_M3b aHi bHi xHi h l e (Z.land yHi MASK48) yLo bExp) ->
    evt rsegs (POST r) (ST 0xb0654 fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) x15 (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 HR. subst r. rewrite normalize_mirror_w. rewrite ?b2z_Zb2z.
    zstep. rewrite (ltb1_eqb0 aSigHi) by lia. zstep. zstep. if_cases Kw; zify_cond Kw; decide_tests_b.
    - change (Z.b2z true) with 1%Z. eapply add_L194; finL.
    - change (Z.b2z false) with 0%Z. zstep. eapply add_L194; finL.
  Qed.

  Lemma add_L0d4 : forall x1 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp yHi yLo bExp r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= yHi < 2^64)%Z -> (0 <= yLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
    r = add_M3b aHi bHi xHi aSigHi aSigLo aExp (Z.land yHi MASK48) yLo bExp ->
    evt rsegs (POST r) (ST 0xb05a4 fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 yHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 yLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 HR. subst r. unfold add_M3b. unfold_sfw.
    zstep. name_reg 6%Z bSigHi.
    zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
    - eapply add_LM4; finL.
    - zstep. eapply add_L2c0; finL.
  Qed.
End Proofs.
