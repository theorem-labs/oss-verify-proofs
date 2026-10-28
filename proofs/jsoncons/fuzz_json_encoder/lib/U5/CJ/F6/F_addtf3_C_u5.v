(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW_add_split.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fe_getround_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_addtf3_A_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_addtf3_B_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Import ListNotations.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SF_buildtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac flia ::= flia_fast.
Local Ltac blia ::= blia_fast.
(* [comment removed for export] *)
Local Ltac step ::= step_fast.
Local Ltac zsimp ::= zsimp_fast.
(* [comment removed for export] *)

(* [comment removed for export] *)
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
  (* [comment removed for export] *)
  Notation ST pc fcx x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR x1 SP gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fcx None m1 (seg_rom rsegs)).


  (* [comment removed for export] *)
  Lemma add_L5a4 : forall x1 x8 x9 x18 x19 x20 x30 x31 (xHi sw aSigHi3 aSigLo aExp bSigHi3 align d2 mask2 sticky newLo r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= sw < 2^64)%Z -> (0 <= aSigHi3 < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi3 < 2^64)%Z -> (0 <= align < 2^64)%Z -> (0 <= d2 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= newLo < 2^64)%Z ->
    (if 9223372036854775808 <=? d2 then 18446744073709551615 else 0)%Z = mask2 ->
    r = align_4 xHi (Z.shiftr sw 63) (Z.lor aSigHi3 2251799813685248) (Z.land (Z.shiftl aSigLo 3) W64) aExp bSigHi3 align mask2 sticky newLo ->
    evt rsegs (POST r) (ST 0xb7228 fc x1 (Z_to_bv 64 align) (Z_to_bv 64 2251799813685248) (Z_to_bv 64 sticky) x8 x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 sw) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigHi3) (Z_to_bv 64 aSigHi3)
                           x18 x19 x20 (Z_to_bv 64 newLo) (Z_to_bv 64 d2) x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 Hm HR. subst r. unfold align_4.
    assert (Rm : (0 <= mask2 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. name_as_by srH (Z.shiftr bSigHi3 (Z.land align 63))
      (change (inr64 (Z.shiftr bSigHi3 (Z.land align 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
    zstep. rewrite (srai63_word d2), Hm by lia.
    zstep. name_reg 16%Z newHi.
    zstep. name_reg 7%Z BLo.
    zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64).
    zstep. name_reg 10%Z AHi.
    unfold add_M6, addsub_mirror. unfold_sfw.
    zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
    - (* [comment removed for export] *) eapply add_Lsub; finL.
    - eapply add_Ladd; finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_L564 : forall x1 x8 x9 x18 x19 x20 x31 (xHi sw aSigHi3 aSigLo aExp bSigHi3 bSigLo3 align d1 mask1 negal outHi r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= sw < 2^64)%Z -> (0 <= aSigHi3 < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    (0 <= bSigHi3 < 2^64)%Z -> (0 <= bSigLo3 < 2^64)%Z -> (0 <= align < 2^64)%Z -> (0 <= d1 < 2^64)%Z -> (0 <= negal < 2^64)%Z -> (0 <= outHi < 2^64)%Z ->
    (if 9223372036854775808 <=? d1 then 18446744073709551615 else 0)%Z = mask1 ->
    r = align_3 xHi (Z.shiftr sw 63) (Z.lor aSigHi3 2251799813685248) (Z.land (Z.shiftl aSigLo 3) W64) aExp bSigHi3 bSigLo3 align mask1 negal outHi ->
    evt rsegs (POST r) (ST 0xb71e8 fc x1 (Z_to_bv 64 align) (Z_to_bv 64 2251799813685248) (Z_to_bv 64 d1) x8 x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 sw) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigHi3) (Z_to_bv 64 aSigHi3)
                           x18 x19 x20 (Z_to_bv 64 bSigLo3) (Z_to_bv 64 negal) (Z_to_bv 64 outHi) x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 Hm HR. subst r. unfold align_3. unfold_sfw. rewrite ?b2z_Zb2z.
    assert (Rm : (0 <= mask1 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. model_reg 29%Z outLoRaw (Z.land (Z.shiftl bSigLo3 (Z.land negal 63)) W64).
    zstep. rewrite (srai63_word d1), Hm by lia.
    zstep. name_reg 7%Z outLo.
    zstep. zstep. name_reg 31%Z n2.
    zstep. name_reg 7%Z lor1. rewrite (zb_negb_eqb0 lor1) by zrange_nonneg.
    zstep. model_reg 29%Z d2 (Z.land (n2 - 64) W64).
    zstep. name_reg 7%Z sticky.
    zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
    - (* [comment removed for export] *)
      zstep. name_as_by srL (Z.shiftr bSigLo3 (Z.land align 63))
        (change (inr64 (Z.shiftr bSigLo3 (Z.land align 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      do 4 zstep. name_reg 28%Z newLo.
      eapply add_L5a4 with (mask2 := 18446744073709551615%Z); finL.
    - zstep. name_as_by newLo (Z.shiftr bSigHi3 (Z.land n2 63))
        (change (inr64 (Z.shiftr bSigHi3 (Z.land n2 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. eapply add_L5a4 with (mask2 := 0%Z); finL.
  Qed.

  (* [comment removed for export] *)
  Lemma add_LM4 : forall x1 x7 x9 x18 x19 x20 x28 x29 x30 x31 (aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp r : Z),
    (0 <= aHi < 2^64)%Z -> (0 <= bHi < 2^64)%Z -> (0 <= xHi < 2^64)%Z -> (0 <= aSigHi < 2^64)%Z -> (0 <= aSigLo < 2^64)%Z ->
    (0 <= aExp < 2^64)%Z -> (0 <= bSigHi < 2^64)%Z -> (0 <= bSigLo < 2^64)%Z -> (0 <= bExp < 2^64)%Z ->
    r = add_M4 aHi bHi xHi aSigHi aSigLo aExp bSigHi bSigLo bExp ->
    evt rsegs (POST r) (ST 0xb7044 fc x1 (Z_to_bv 64 bExp) (Z_to_bv 64 bSigHi) x7 (Z_to_bv 64 bHi) x9
                           (Z_to_bv 64 aSigLo) (Z_to_bv 64 aHi) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) (Z_to_bv 64 bSigLo) (Z_to_bv 64 aSigHi)
                           x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 R8 R9 HR. subst r. unfold add_M4. unfold align_mirror. unfold_sfw.
    zstep. name_reg 11%Z sw.
    do 6 zstep. name_reg 17%Z aSigHi3.
    zstep. zstep. model_reg 28%Z bSigLo3 (Z.land (Z.shiftl bSigLo 3) W64).
    zstep. zstep. name_reg 16%Z bSigHi3.
    zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
    - (* [comment removed for export] *)
      zstep. model_reg 5%Z align (Z.land (aExp - bExp) W64).
      zstep. zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
      + (* [comment removed for export] *)
        zstep. zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64). zstep. name_reg 10%Z AHi.
        unfold add_M6, addsub_mirror. unfold_sfw.
        zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
        * eapply add_Ladd; finL.
        * eapply add_Lsub; finL.
      + (* [comment removed for export] *)
        do 4 zstep. rewrite (landM32_swrap_land64 (128 - align)). name_reg 30%Z n1.
        zstep. model_reg 7%Z d1 (Z.land (n1 - 64) W64).
        zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - align)).
        name_as_by negal (sext32 (0 - align)) (apply sext32_range).
        zstep. if_cases Kd; zify_cond Kd; decide_tests_b.
        * (* [comment removed for export] *)
          zstep. zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr bSigLo3 1) (Z.land (Z.lxor n1 W64) 63))
            (change (inr64 (Z.shiftr (Z.shiftr bSigLo3 1) (Z.land (Z.lxor n1 W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
          zstep. name_reg 30%Z outHi.
          eapply add_L564 with (mask1 := 18446744073709551615%Z); finL.
        * zstep. model_reg 30%Z outHi (Z.land (Z.shiftl bSigLo3 (Z.land n1 63)) W64). zstep.
          eapply add_L564 with (mask1 := 0%Z); finL.
    - (* [comment removed for export] *)
      zstep. zstep. model_reg 5%Z ALo (Z.land (Z.shiftl aSigLo 3) W64). zstep. name_reg 10%Z AHi.
      unfold add_M6, addsub_mirror. unfold_sfw.
      zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
      + eapply add_Ladd; finL.
      + zstep. eapply add_Lsub; finL.
  Qed.
End Proofs.
