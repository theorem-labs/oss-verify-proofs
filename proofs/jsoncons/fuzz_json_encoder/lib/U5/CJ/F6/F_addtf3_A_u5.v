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

Definition addtf3_entry := 0xb6c9c%Z.

(* [comment removed for export] *)
Definition addtf3_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (R : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (lo64 R)) (Z_to_bv 64 (hi64 R)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ frm0 fc'
    /\ stk rsegs m' (bv_unsigned sp - 48) (bv_unsigned sp).

Ltac unfold_sfw := cbv beta delta [add64 sub64 shl64 not64 is_neg64 sra63 lt_s64 eqz64 nez64 zext32 lo64 hi64 wrap64
                                   ONES64 M32 SIGN64 MASK48 MASKLO ABS_HI INF_HI QUIET_HI QNAN_HI IMPLICIT_HI IMPL3_HI SPEC_K].

  Ltac showregs := let x10 := getreg 10%Z in let x11 := getreg 11%Z in let x12 := getreg 12%Z in let x13 := getreg 13%Z in let x14 := getreg 14%Z in let x15 := getreg 15%Z in let x16 := getreg 16%Z in let x17 := getreg 17%Z in let x5 := getreg 5%Z in let x6 := getreg 6%Z in let x7 := getreg 7%Z in let x8 := getreg 8%Z in let x9 := getreg 9%Z in let x18 := getreg 18%Z in let x19 := getreg 19%Z in let x20 := getreg 20%Z in let x28 := getreg 28%Z in let x29 := getreg 29%Z in
    idtac "a0=" x10; idtac "a1=" x11; idtac "a2=" x12; idtac "a3=" x13; idtac "a4=" x14; idtac "a5=" x15; idtac "a6=" x16; idtac "a7=" x17; idtac "t0=" x5; idtac "t1=" x6; idtac "t2=" x7; idtac "s0=" x8; idtac "s1=" x9; idtac "s2=" x18; idtac "s3=" x19; idtac "s4=" x20; idtac "t3=" x28; idtac "t4=" x29.

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
  Lemma add_Lret : forall fcx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 (lo hi r : Z),
    frm0 fcx -> (0 <= lo < 2^64)%Z -> (0 <= hi < 2^64)%Z ->
    r = mk128 hi lo ->
    evt rsegs (POST r) (ST 0xb7420 fcx x1 x5 x6 x7 (Z_to_bv 64 hi) (Z_to_bv 64 lo) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR MI MU STK WM.
    intros until r. intros FRMx Rlo Rhi HR. subst r.
    pose proof FR as FR'. pose proof STK as ST'.
    do 10 zstep.
    release_frame FR' ST' (bv_unsigned sp).
    replace (bv_unsigned sp + -48)%Z with (bv_unsigned sp - 48)%Z in ST' by lia.
    sf_finish.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma add_Lround : forall x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x28 x29 x30 x31 (SHi SLo aExp signHi r : Z),
    (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= signHi < 2^64)%Z ->
    r = round_mirror SHi SLo aExp signHi ->
    evt rsegs (POST r) (ST 0xb7394 fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 (Z_to_bv 64 aExp) x16 x17 (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 HR. subst r. unfold round_mirror. unfold_sfw. rewrite ?b2z_Zb2z.
    zstep. name_reg 19%Z rgs.
    do 5 zstep. name_reg 20%Z resLo0.
    do 2 zstep. zstep. showregs. name_reg 9%Z resLo. zstep. name_reg 8%Z resHi.
    zstep. call fe_getround_spec. 1-2: assumption.
    zstep. zstep. if_cases Kc; zify_cond Kc; [exfalso; clear -Kc; lia|].
    zstep. zstep. if_cases Kc2; zify_cond Kc2; [exfalso; clear -Kc2; lia|].
    zstep. if_cases Kc3; zify_cond Kc3. { exfalso. clear -Kc3. lia. }
    zstep. zstep. if_cases Kt; zify_cond Kt; decide_tests_b.
    - (* [comment removed for export] *)
      zstep. zstep. rewrite lxor1_b2z. name_reg 10%Z inc. zstep.
      zstep. model_reg 10%Z sumLo (Z.land (resLo + inc) W64).
      zstep. zstep. model_reg 8%Z resHi2 (Z.land (resHi + Z.b2z (sumLo <? resLo)) W64).
      zstep. zstep. if_cases Kz; zify_cond Kz.
      + (* [comment removed for export] *)
        eapply add_Lret; [exact FRM | zrange | zrange | reflexivity].
      + zstep. call fe_raise_inexact_spec. 1-2: assumption.
        eapply add_Lret; [assumption | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      zstep. name_reg 10%Z inc.
      zstep. model_reg 10%Z sumLo (Z.land (resLo + inc) W64).
      zstep. zstep. model_reg 8%Z resHi2 (Z.land (resHi + Z.b2z (sumLo <? resLo)) W64).
      zstep. zstep. zstep. call fe_raise_inexact_spec. 1-2: assumption.
      eapply add_Lret; [assumption | zrange | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_L704 : forall x1 x6 x7 x8 x9 x10 x14 x15 x19 x20 x28 x29 x30 x31 (signHi hiSh mask4 sticky newLo r : Z),
    (0 <= signHi < 2^64)%Z -> (0 <= hiSh < 2^64)%Z -> (0 <= mask4 < 2^64)%Z -> (0 <= sticky < 2^64)%Z -> (0 <= newLo < 2^64)%Z ->
    r = denorm_3 signHi hiSh mask4 sticky newLo ->
    evt rsegs (POST r) (ST 0xb7388 fc x1 (Z_to_bv 64 mask4) x6 x7 x8 x9 x10 (Z_to_bv 64 newLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 x15 (Z_to_bv 64 hiSh) (Z_to_bv 64 sticky) (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 HR. subst r. unfold denorm_3.
    do 3 zstep.
    eapply add_Lround; [zrange | zrange | lia | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_L6c0 : forall x1 x5 x6 x7 x8 x9 x19 x20 x28 x29 x30 x31 (signHi SHi SLo shift d3 mask3 t outHi r : Z),
    (0 <= signHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= shift < 2^64)%Z ->
    (0 <= d3 < 2^64)%Z -> (0 <= t < 2^64)%Z -> (0 <= outHi < 2^64)%Z ->
    (if 9223372036854775808 <=? d3 then 18446744073709551615 else 0)%Z = mask3 ->
    r = denorm_2 signHi SHi SLo shift mask3 t outHi ->
    evt rsegs (POST r) (ST 0xb7344 fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 shift) (Z_to_bv 64 t) (Z_to_bv 64 d3) (Z_to_bv 64 outHi) (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 R5 R6 R7 Hm HR. subst r. unfold denorm_2. unfold_sfw. rewrite ?b2z_Zb2z.
    assert (Rm3 : (0 <= mask3 < 2^64)%Z) by (rewrite <- Hm; destruct (Z.leb _ _); lia).
    zstep. rewrite (srai63_word d3), Hm by lia.
    zstep. name_as_by hiSh (Z.shiftr SHi (Z.land shift 63))
      (change (inr64 (Z.shiftr SHi (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
    zstep. zstep. name_reg 5%Z outLo.
    zstep. name_reg 15%Z n3.
    zstep. name_reg 17%Z lor1. rewrite (zb_negb_eqb0 lor1) by zrange_nonneg.
    zstep. model_reg 6%Z d4 (Z.land (n3 - 64) W64).
    rewrite (sra63_leb d4) by lia.
    zstep. name_reg 17%Z sticky.
    zstep. rewrite (srai63_word d4) by lia. name_reg 5%Z mask4.
    zstep. if_cases K4; zify_cond K4; decide_tests_b.
    - (* [comment removed for export] *)
      zstep. name_as_by sr1 (Z.shiftr SLo (Z.land shift 63))
        (change (inr64 (Z.shiftr SLo (Z.land shift 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      do 4 zstep. name_reg 11%Z newLo.
      eapply add_L704; [zrange | zrange | zrange | zrange | zrange | reflexivity].
    - zstep. name_as_by newLo (Z.shiftr SHi (Z.land n3 63))
        (change (inr64 (Z.shiftr SHi (Z.land n3 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
      zstep. eapply add_L704; [zrange | zrange | zrange | zrange | zrange | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_LM8 : forall x1 x5 x6 x7 x8 x9 x14 x16 x17 x19 x20 x28 x29 x30 x31 (SHi SLo aExp signHi r : Z),
    (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z -> (0 <= signHi < 2^64)%Z ->
    r = add_M8 SHi SLo aExp signHi ->
    evt rsegs (POST r) (ST 0xb7300 fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) x14 (Z_to_bv 64 aExp) x16 x17 (Z_to_bv 64 signHi) x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 HR. subst r. unfold add_M8. unfold_sfw.
    zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_tests_b.
    - (* [comment removed for export] *) eapply add_Lround; [zrange | zrange | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      unfold denorm_mirror. unfold_sfw. rewrite ?b2z_Zb2z.
      do 3 zstep. model_reg 14%Z shift (Z.land (1 - aExp) W64).
      zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (0 - shift)).
      name_as_by negsh (sext32 (0 - shift)) (apply sext32_range).
      zstep. model_reg 16%Z d3 (Z.land (64 - shift) W64).
      zstep. model_reg 15%Z t (Z.land (Z.shiftl SLo (Z.land negsh 63)) W64).
      zstep. if_cases K3; zify_cond K3; decide_tests_b.
      + (* [comment removed for export] *)
        zstep. zstep. zstep. rewrite Z_to_bv_swrap32. rewrite (sext32_land64 (128 - shift)).
        name_as_by mm (sext32 (128 - shift)) (apply sext32_range).
        zstep. zstep. zstep. name_as_by sr0 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor mm W64) 63))
          (change (inr64 (Z.shiftr (Z.shiftr SLo 1) (Z.land (Z.lxor mm W64) 63))); apply zr_shiftr; [zrange | apply Z.land_nonneg; right; lia]).
        zstep. name_reg 17%Z outHi.
        eapply add_L6c0 with (mask3 := 18446744073709551615%Z);
          [zrange | zrange | zrange | zrange | zrange | zrange | zrange | decide_tests_b; reflexivity | reflexivity].
      + (* [comment removed for export] *)
        zstep. zstep.
        eapply add_L6c0 with (mask3 := 0%Z);
          [zrange | zrange | zrange | zrange | zrange | zrange | zrange | decide_tests_b; reflexivity | reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma add_LM7 : forall x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x28 x29 x30 x31 (xHi SHi SLo aExp r : Z),
    (0 <= xHi < 2^64)%Z -> (0 <= SHi < 2^64)%Z -> (0 <= SLo < 2^64)%Z -> (0 <= aExp < 2^64)%Z ->
    r = add_M7 xHi SHi SLo aExp ->
    evt rsegs (POST r) (ST 0xb7278 fc x1 x5 x6 x7 x8 x9 (Z_to_bv 64 SHi) (Z_to_bv 64 SLo) (Z_to_bv 64 (-1)) (Z_to_bv 64 281474976710655) (Z_to_bv 64 xHi) (Z_to_bv 64 aExp) x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Proof using FR FRM MI MU STK WM.
    intros until r. intros R1 R2 R3 R4 HR. subst r. unfold add_M7. unfold_sfw.
    do 3 zstep. zstep. model_reg 18%Z signHi (Z.land (Z.shiftl (Z.shiftr xHi 63) 63) W64).
    zstep. if_cases K; rewrite ?bv_lts_lxor in K; zify_cond K; decide_tests_b.
    - (* [comment removed for export] *) eapply add_LM8; [zrange | zrange | zrange | zrange | reflexivity].
    - (* [comment removed for export] *)
      do 5 zstep. eapply add_Lret; [exact FRM | lia | zrange | reflexivity].
  Qed.
End Proofs.
