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
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.F10 Require Import F_addtf3_D_u.
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

Ltac reg_eq_ev := first [ reflexivity | (symmetry; apply Z_to_bv_bv_unsigned) | apply Z_to_bv_bv_unsigned ].
Ltac tree_eq_ev :=
  first [ reflexivity
        | lazymatch goal with
          | |- TNode _ _ _ = TNode _ _ _ => f_equal; tree_eq_ev
          | |- Some _ = Some _ => f_equal; reg_eq_ev
          | |- _ => reg_eq_ev
          end ].
Ltac ms_eq_ev :=
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => unfold mkR; f_equal; [ tree_eq_ev | reflexivity .. ]
  end.

Ltac jump L := eapply evt_eq; [ | eapply L ]; first [ ms_eq_ev | finL ].

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

  Lemma add_LM1 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_M1 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt rsegs (POST r) (ST 0xb0568 fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 HR. subst r. unfold add_M1. pose_word_ranges.
    zstep. zstep. if_cases Ke; zify_cond Ke; decide_tests_b.
    -
      do 3 zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
      +
        unfold add_M2. unfold_sfw.
        do 8 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
        * jump add_L184.
        * jump add_L0d4.
      + unfold add_M2. unfold_sfw.
        do 7 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
        * jump add_L0d4.
        * jump add_L184.
    - do 3 zstep. if_cases Ks; zify_cond Ks; decide_tests_b.
      +
        unfold add_M2. unfold_sfw.
        do 7 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
        * jump add_L0d4.
        * jump add_L184.
      + unfold add_M2. unfold_sfw.
        do 8 zstep. name_reg 15%Z aExp. name_reg 5%Z bExp. zstep.
        zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
        * jump add_L184.
        * jump add_L0d4.
  Qed.

  Lemma add_L108 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_S3 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt rsegs (POST r) (ST 0xb05d8 fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_S3. unfold_sfw. rewrite ?b2z_Zb2z.
    do 4 zstep. zstep. if_cases Ki; zify_cond Ki; decide_tests_b.
    -
      zstep. zstep. zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
      +   jump add_Lret.
      + zstep. zstep. if_cases Kz; zify_cond Kz; decide_tests_b.
        *
          zstep. zstep. if_cases Kbz; zify_cond Kbz; decide_tests_b.
          --   jump add_Lret.
          --   do 3 zstep. jump add_Lret.
        * zstep. zstep. if_cases Kbz; zify_cond Kbz; decide_tests_b.
          --   eapply add_LM1; finL.
          --   do 3 zstep. jump add_Lret.
    -
      do 6 zstep. name_reg 9%Z xw.
      zstep. rewrite (ltb1_eqb0 xw) by zrange_nonneg. zstep. if_cases Kx; zify_cond Kx; decide_tests_b.
      +
        zstep. replace (Z_to_bv 64 (Z.b2z false + -1)) with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
        change (Z.land (Z.b2z false - 1) 18446744073709551615) with 18446744073709551615%Z.
        do 3 zstep. jump add_Lret.
      +
        zstep. zstep. zstep. replace (Z_to_bv 64 (Z.b2z true + -1)) with (Z_to_bv 64 0) by (apply Z_to_bv_eqm; reflexivity).
        change (Z.land (Z.b2z true - 1) 18446744073709551615) with 0%Z.
        do 3 zstep. jump add_Lret.
  Qed.

  Lemma add_L0f4 : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_S2 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt rsegs (POST r) (ST 0xb05c4 fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_S2. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb; decide_tests_b.
    -
      zstep. rewrite (ltb1_eqb0 (bv_unsigned wb0)) by lia. zstep. if_cases Kbl; zify_cond Kbl; decide_tests_b.
      +   eapply add_L108; finL.
      +   do 4 zstep. jump add_Lret.
    - zstep. zstep. if_cases Kbl; zify_cond Kbl; decide_tests_b.
      +   do 4 zstep. jump add_Lret.
      + eapply add_L108; finL.
  Qed.

  Lemma add_LS : forall x1 x5 x6 x7 x12 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_S (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt rsegs (POST r) (ST 0xb05b0 fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 x12 (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges.
    unfold add_S. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. zstep. zstep. if_cases Ka; zify_cond Ka; decide_tests_b.
    -
      zstep. rewrite (ltb1_eqb0 (bv_unsigned wa0)) by lia. zstep. if_cases Kal; zify_cond Kal; decide_tests_b.
      +   eapply add_L0f4; finL.
      +   do 5 zstep. jump add_Lret.
    - zstep. zstep. if_cases Kal; zify_cond Kal; decide_tests_b.
      +   do 5 zstep. jump add_Lret.
      + eapply add_L0f4; finL.
  Qed.

  Lemma add_L074 : forall x1 x5 x6 x7 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (aAbsHi bAbsHi r : Z),
    (0 <= aAbsHi < 2^64)%Z -> (0 <= bAbsHi < 2^64)%Z ->
    r = add_top2 (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) aAbsHi bAbsHi ->
    evt rsegs (POST r) (ST 0xb0544 fc x1 x5 x6 x7 wb1 wb0 wa0 wa1 (Z_to_bv 64 9223653511831486464) (Z_to_bv 64 aAbsHi) (Z_to_bv 64 bAbsHi) x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 HR. subst r. pose_word_ranges. unfold add_top2. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. model_reg 12%Z tb (Z.land (bAbsHi + 9223653511831486464) W64).
    zstep. zstep. zstep. if_cases Kt; zify_cond Kt; decide_tests_b.
    -
      zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
      +   eapply add_LS; finL.
      + eapply add_LM1; finL.
    - zstep. zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
      + eapply add_LM1; finL.
      + zstep. eapply add_LS; finL.
  Qed.

  Lemma add_L034 : forall x5 x6 x7 x8 x9 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (wa0 wa1 wb0 wb1 : word) (r : Z),
    r = add_top (bv_unsigned wa0) (bv_unsigned wa1) (bv_unsigned wb0) (bv_unsigned wb1) ->
    evt rsegs (POST r) (ST 0xb0504 fc ra x5 x6 x7 x8 x9 wa0 wa1 wb0 wb1 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros HR. subst r. pose_word_ranges. unfold add_top. unfold_sfw. rewrite ?b2z_Zb2z.
    do 5 zstep. name_reg 13%Z aAbsHi.
    zstep. zstep. zstep. if_cases K0; zify_cond K0; decide_tests_b.
    -
      zstep. rewrite (ltb1_eqb0 (bv_unsigned wa0)) by lia. zstep. name_reg 14%Z bAbsHi.
      zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
      +   eapply add_LS; finL.
      + eapply add_L074; finL.
    - zstep. zstep. zstep. name_reg 14%Z bAbsHi.
      zstep. if_cases Kl; zify_cond Kl; decide_tests_b.
      + eapply add_L074; finL.
      + zstep. eapply add_LS; finL.
  Qed.
End Proofs.

Lemma addtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  frm0 fc ->
  evt rsegs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (f128_add (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb04e8) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST MI FRM.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  assert (SPLO : (48 <= bv_unsigned sp)%Z) by (destruct ST as [? _]; lia).
  pose_word_ranges.
  rewrite f128_add_split by lia.
  carve_frame 48%nat ST.
  do 7 zstep.
  eapply add_L034; try eassumption; reflexivity.
Qed.
