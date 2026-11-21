(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel CkMathAdler CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit AdlAGlue AdlA_zs.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Definition adl_FRAMET (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : amem) : Prop := exists j1 j2,
  rw_cells asegs m1 (bv_unsigned sp + -160)
    [CB 32 j1; C8 (Z_to_bv 64 0xfea0); CB 16 j2; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma adl_FRAMET_C : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1,
  adl_FRAMET sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 -> adl_FRAMEC sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1.
Proof.
  intros sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 (j1 & j2 & F).
  exists (cells_bytes [CB 32 j1; C8 (Z_to_bv 64 0xfea0); CB 16 j2]).
  exact (rw_cells_merge asegs m1 _ [] [CB 32 j1; C8 (Z_to_bv 64 0xfea0); CB 16 j2] _ F).
Qed.

Lemma adl_INVT_INV : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo A bs m1,
  adl_INVG (adl_FRAMET sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp m lo A bs m1 ->
  adl_INVG (adl_FRAMEC sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp m lo A bs m1.
Proof. intros until m1. intros (F & R). split; [apply adl_FRAMET_C; exact F| exact R]. Qed.

Lemma bz_skipn16 : forall bs i, 0 <= i -> i + 16 <= Z.of_nat (length bs) ->
  skipn (Z.to_nat i) bs =
  bz bs i :: bz bs (i+1) :: bz bs (i+2) :: bz bs (i+3) :: bz bs (i+4) :: bz bs (i+5) :: bz bs (i+6) :: bz bs (i+7)
  :: bz bs (i+8) :: bz bs (i+9) :: bz bs (i+10) :: bz bs (i+11) :: bz bs (i+12) :: bz bs (i+13) :: bz bs (i+14) :: bz bs (i+15)
  :: skipn (Z.to_nat (i + 16)) bs.
Proof.
  intros bs i I0 IL. unfold bz. rewrite (skipn16 bs (Z.to_nat i)) by lia.
  replace (Z.to_nat (i+1)) with (Z.to_nat i + 1)%nat by lia. replace (Z.to_nat (i+2)) with (Z.to_nat i + 2)%nat by lia.
  replace (Z.to_nat (i+3)) with (Z.to_nat i + 3)%nat by lia. replace (Z.to_nat (i+4)) with (Z.to_nat i + 4)%nat by lia.
  replace (Z.to_nat (i+5)) with (Z.to_nat i + 5)%nat by lia. replace (Z.to_nat (i+6)) with (Z.to_nat i + 6)%nat by lia.
  replace (Z.to_nat (i+7)) with (Z.to_nat i + 7)%nat by lia. replace (Z.to_nat (i+8)) with (Z.to_nat i + 8)%nat by lia.
  replace (Z.to_nat (i+9)) with (Z.to_nat i + 9)%nat by lia. replace (Z.to_nat (i+10)) with (Z.to_nat i + 10)%nat by lia.
  replace (Z.to_nat (i+11)) with (Z.to_nat i + 11)%nat by lia. replace (Z.to_nat (i+12)) with (Z.to_nat i + 12)%nat by lia.
  replace (Z.to_nat (i+13)) with (Z.to_nat i + 13)%nat by lia. replace (Z.to_nat (i+14)) with (Z.to_nat i + 14)%nat by lia.
  replace (Z.to_nat (i+15)) with (Z.to_nat i + 15)%nat by lia. replace (Z.to_nat (i+16)) with (Z.to_nat i + 16)%nat by lia.
  reflexivity.
Qed.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (adler A n : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 160.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis AR : 0 <= adler < 2^64.
  Hypothesis A1R : 1 <= A.
  Hypothesis NL : Z.of_nat (length bs) = n.
  Hypothesis ALO : A + n <= lo.
  Hypothesis BF : Forall (fun b => 0 <= b < 256) bs.
  Hypothesis UNP : unpoisoned m A (A + n).
  Hypothesis RB : rng RNG A n.
  Hypothesis RS : shrng RNG A (A + n).
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 160, SP)].
  Notation POST res := (ck_postA 160 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation FRAMEC := (adl_FRAMEC sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation FRAMET := (adl_FRAMET sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
  Notation INV := (adl_INVG FRAMEC sp m lo A bs).
  Notation INVT := (adl_INVG FRAMET sp m lo A bs).
  Notation W_above := (adl_W_above sp).
  Notation adl_epi' := (adl_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo adler A n bs
                                LOS KLO AR A1R NL ALO BF UNP RB RS RI RSTK).

  Lemma adl_fin_comb : forall sa sb res m1 (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    0 <= sa < 65536 -> 0 <= sb < 65536 -> res = adl_resc (sa, sb) -> INVT m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 sb) x16 (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x825c8) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros sa sb res m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 SA SB RES INV1.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    do 2 zstep.
    setreg 10 (Z_to_bv 64 res) ltac:(f_equal; rewrite RES; unfold adl_resc; cbn [fst snd]; rewrite shl16_small by lia; reflexivity).
    apply adl_epi'. apply adl_INVT_INV. exact INV1.
  Qed.

  Lemma adl_fin_mod : forall sa sb res m1 (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    0 <= sa < 2^62 -> 0 <= sb < 2^62 -> res = adl_resm (sa, sb) -> INVT m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 sb) x16 (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x82580) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros sa sb res m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 SA SB RES INV1.
    pose proof INV1 as ((j1 & j2 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    do 3 zstep.
    setreg 11 (Z_to_bv 64 (amag_t sa)) ltac:(f_equal; symmetry; apply amag_t_mach; lia).
    zstep.
    setreg 10 (Z_to_bv 64 (amag_t sb)) ltac:(f_equal; symmetry; apply amag_t_mach; lia).
    pose proof (amag_t_range sa ltac:(lia)) as TRa. pose proof (amag_v_range sa ltac:(lia)) as VRa.
    pose proof (amag_q_range sa ltac:(lia)) as QRa. unfold amag_q in QRa.
    pose proof (amag_t_range sb ltac:(lia)) as TRb. pose proof (amag_v_range sb ltac:(lia)) as VRb.
    pose proof (amag_q_range sb ltac:(lia)) as QRb. unfold amag_q in QRb.
    do 14 zstep.
    setreg 17 (Z_to_bv 64 (sa mod 65521)) ltac:(f_equal; change 65521 with BASE at 1; rewrite <- (amag_mod sa) by lia; unfold amag_q; reflexivity).
    setreg 15 (Z_to_bv 64 (sb mod 65521)) ltac:(f_equal; change 65521 with BASE at 1; rewrite <- (amag_mod sb) by lia; unfold amag_q; reflexivity).
    pose proof (mod_BASE_range sa) as MRa. pose proof (mod_BASE_range sb) as MRb. unfold BASE in MRa, MRb.
    eapply adl_fin_comb; [ | | | exact INV1]; [lia | lia | rewrite RES; apply adl_resm_resc].
  Qed.

  Lemma adl_tail_loop : forall (k : nat) i i0 sa sb res m1
      (x1 x5 x6 x7 x8 x9 x10 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    Z.of_nat k = n - i -> 0 <= i0 <= i -> 1 <= n - i -> n - i0 <= 5552 ->
    0 <= sa <= 65535 + 255 * (i - i0) -> 0 <= sb <= 65535 + 1481295 * (i - i0) ->
    res = adl_resm (adler_fold (sa, sb) (skipn (Z.to_nat i) bs)) ->
    INVT m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (A + i)))
          FR (Z_to_bv 64 0x82618) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction k as [|k IH]; intros i i0 sa sb res m1 x1 x5 x6 x7 x8 x9 x10 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
                                   HK I0 IN N0 SA SB RES INV1; [lia|].
    pose proof INV1 as ((j1 & j2 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) (A + i) 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
    do 3 zstep. rewrite sxb_sval. zstep.
    ck_branch 10 0x82628 CK.
    pose proof (ck_buf_read m1 A bs i _ BY ltac:(lia) eq_refl) as RDB.
    pose proof (bz_range bs i BF) as BR.
    zstep. cbv beta. rewrite (bz_val bs i BF).
    do 6 zstep.
    rewrite (bz_skipn bs i ltac:(lia)) in RES. rewrite adler_fold_cons in RES.
    replace (sb + (sa + bz bs i)) with (sa + bz bs i + sb) in RES by lia.
    if_cases KB; zify_cond KB.
    - replace (A + i + 1) with (A + (i + 1)) by lia. replace (n - i + -1) with (n - (i + 1)) by lia.
      eapply (IH (i + 1) i0); [lia|lia|lia|lia| | |exact RES|exact INV1]; lia.
    - zstep.
      replace (Z.to_nat (i + 1)) with (length bs) in RES by lia. rewrite skipn_all in RES. cbn [adler_fold] in RES.
      eapply adl_fin_mod; [ | | exact RES | exact INV1]; lia.
  Qed.

  Local Ltac ckK m1 MU BY a ib U JOIN :=
    let b := fresh "b" in let RD := fresh "RD" in let CK := fresh "CK" in let SR := fresh "SR" in let RDB := fresh "RDB" in
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) a 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR);
    pose proof (ck_buf_read m1 A bs ib _ BY ltac:(lia) eq_refl) as RDB;
    do 4 zstep; rewrite sxb_sval; zstep; cbv beta; rewrite (bz_val bs ib BF); zstep;
    ck_branch U JOIN CK; clear RD CK SR RDB.

  Lemma adl_do16_tail : forall (k : nat) i0 j sa sb res m1
      (x1 x5 x8 x9 x10 x11 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 : word),
    Z.of_nat k >= n - i0 - j -> 0 <= i0 -> 0 <= j -> 16 <= n - i0 - j -> n - i0 <= 5552 ->
    0 <= sa <= 65535 + 255 * j -> 0 <= sb <= 65535 + 1481295 * j ->
    res = adl_resm (adler_fold (sa, sb) (skipn (Z.to_nat (i0 + j)) bs)) ->
    INVT m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 (Z_to_bv 64 (Z.shiftr (A + i0 + j) 3 + 2147450880)) (Z_to_bv 64 (n - i0 - j)) x8 x9 x10 x11 (Z_to_bv 64 (n - i0)) x13 (Z_to_bv 64 j)
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 15) x29 x30 (Z_to_bv 64 (A + i0)))
          FR (Z_to_bv 64 0x822ac) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction k as [|k IH]; intros i0 j sa sb res m1 x1 x5 x8 x9 x10 x11 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30
                                   HK I0 J0 L16 N0 SA SB RES INV1; [lia|].
    pose proof INV1 as ((j1 & j2 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) (A + i0 + j) 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
    zstep. rewrite sxb_sval. do 2 zstep.
    ck_branch 10 0x822b8 CK. clear RD CK SR.
    ckK m1 MU BY (A + i0 + j + 1) (i0 + j) 29 0x822d0.
    pose proof (bz_range bs (i0 + j) BF) as BR0.
    ckK m1 MU BY (A + i0 + j + 2) (i0 + j + 1) 30 0x822e8.
    pose proof (bz_range bs (i0 + j + 1) BF) as BR1.
    ckK m1 MU BY (A + i0 + j + 3) (i0 + j + 2) 8 0x82300.
    pose proof (bz_range bs (i0 + j + 2) BF) as BR2.
    ckK m1 MU BY (A + i0 + j + 4) (i0 + j + 3) 9 0x82318.
    pose proof (bz_range bs (i0 + j + 3) BF) as BR3.
    ckK m1 MU BY (A + i0 + j + 5) (i0 + j + 4) 18 0x82330.
    pose proof (bz_range bs (i0 + j + 4) BF) as BR4.
    ckK m1 MU BY (A + i0 + j + 6) (i0 + j + 5) 19 0x82348.
    pose proof (bz_range bs (i0 + j + 5) BF) as BR5.
    ckK m1 MU BY (A + i0 + j + 7) (i0 + j + 6) 20 0x82360.
    pose proof (bz_range bs (i0 + j + 6) BF) as BR6.
    ckK m1 MU BY (A + i0 + j + 8) (i0 + j + 7) 21 0x82378.
    pose proof (bz_range bs (i0 + j + 7) BF) as BR7.
    ckK m1 MU BY (A + i0 + j + 9) (i0 + j + 8) 22 0x82390.
    pose proof (bz_range bs (i0 + j + 8) BF) as BR8.
    ckK m1 MU BY (A + i0 + j + 10) (i0 + j + 9) 23 0x823a8.
    pose proof (bz_range bs (i0 + j + 9) BF) as BR9.
    ckK m1 MU BY (A + i0 + j + 11) (i0 + j + 10) 24 0x823c0.
    pose proof (bz_range bs (i0 + j + 10) BF) as BR10.
    ckK m1 MU BY (A + i0 + j + 12) (i0 + j + 11) 25 0x823d8.
    pose proof (bz_range bs (i0 + j + 11) BF) as BR11.
    ckK m1 MU BY (A + i0 + j + 13) (i0 + j + 12) 26 0x823f0.
    pose proof (bz_range bs (i0 + j + 12) BF) as BR12.
    ckK m1 MU BY (A + i0 + j + 14) (i0 + j + 13) 27 0x82408.
    pose proof (bz_range bs (i0 + j + 13) BF) as BR13.
    ckK m1 MU BY (A + i0 + j + 15) (i0 + j + 14) 1 0x82420.
    pose proof (bz_range bs (i0 + j + 14) BF) as BR14.
    pose proof (ck_buf_read m1 A bs (i0 + j + 15) _ BY ltac:(lia) eq_refl) as RDB.
    pose proof (bz_range bs (i0 + j + 15) BF) as BR15.
    do 2 zstep. zstep. cbv beta. rewrite (bz_val bs (i0 + j + 15) BF). clear RDB.
    do 34 zstep.
    rewrite (bz_skipn16 bs (i0 + j) ltac:(lia) ltac:(lia)) in RES. rewrite adler_fold_16 in RES.
    replace (i0 + j + 16) with (i0 + (j + 16)) in RES by lia.
    if_cases KB; zify_cond KB.
    -
      replace (n - i0 - j + -16) with (n - i0 - (j + 16)) by lia.
      replace (Z.shiftr (A + i0 + j) 3 + 2147450882) with (Z.shiftr (A + i0 + (j + 16)) 3 + 2147450880)
        by (replace (A + i0 + (j + 16)) with (A + i0 + j + 16) by lia; rewrite shiftr3_add16; lia).
      eapply (IH i0 (j + 16)); [lia|lia|lia|lia|lia| | | eapply adl_resm_eq; [ | | exact RES] |exact INV1]; lia.
    -
      zstep. zstep.
      if_cases KC; zify_cond KC.
      +
        do 3 zstep.
        replace (A + i0 + (j + 16)) with (A + (i0 + (j + 16))) by lia.
        replace (n - i0 - j + -16) with (n - (i0 + (j + 16))) by lia.
        eapply (adl_tail_loop (Z.to_nat (n - (i0 + (j + 16)))) (i0 + (j + 16)) i0);
          [lia|lia|lia|lia| | | eapply adl_resm_eq; [ | | exact RES] |exact INV1]; lia.
      +
        replace (Z.to_nat (i0 + (j + 16))) with (length bs) in RES by lia. rewrite skipn_all in RES. cbn [adler_fold] in RES.
        eapply adl_fin_mod; [ | | eapply adl_resm_eq0; [ | | exact RES] | exact INV1]; lia.
  Qed.

  Lemma adl_tail_setup : forall i0 sa sb res m1
      (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    0 <= i0 -> 16 <= n - i0 -> n - i0 <= 5552 -> 0 <= sa <= 65535 -> 0 <= sb <= 65535 ->
    res = adl_resm (adler_fold (sa, sb) (skipn (Z.to_nat i0) bs)) ->
    INVT m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (n - i0)) x13 x14
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (A + i0)))
          FR (Z_to_bv 64 0x82298) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros i0 sa sb res m1 x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 I0 L16 N0 SA SB RES INV1.
    pose proof INV1 as ((j1 & j2 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    do 5 zstep.
    setreg 6 (Z_to_bv 64 (Z.shiftr (A + i0 + 0) 3 + 2147450880)) ltac:(f_equal; rewrite Z.add_0_r; lia).
    replace (n - i0) with (n - i0 - 0) at 1 by lia.
    replace (Z.to_nat i0) with (Z.to_nat (i0 + 0)) in RES by lia.
    eapply (adl_do16_tail (Z.to_nat (n - i0)) i0 0); [lia|lia|lia|lia|lia| | |exact RES|exact INV1]; lia.
  Qed.

  Lemma skipn_nonnil : forall i, 0 <= i < n -> skipn (Z.to_nat i) bs <> [].
  Proof using NL.
    intros i Hi E. assert (L : length (skipn (Z.to_nat i) bs) = 0%nat) by (rewrite E; reflexivity).
    rewrite length_skipn in L. lia.
  Qed.

  Lemma adl_after_blocks : forall i0 sa sb res m1
      (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    0 <= i0 <= n -> n - i0 < 5552 -> 0 <= sa < 65521 -> 0 <= sb < 65521 ->
    res = adl_blocks_res 0 (sa, sb) (skipn (Z.to_nat i0) bs) ->
    INVT m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 (Z_to_bv 64 (n - i0)) x13 x14
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 (A + i0)))
          FR (Z_to_bv 64 0x8228c) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros i0 sa sb res m1 x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 I0 N0 SA SB RES INV1.
    pose proof INV1 as ((j1 & j2 & FRM) & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    zstep. if_cases K0; zify_cond K0.
    -
      replace (Z.to_nat i0) with (length bs) in RES by lia. rewrite skipn_all, adl_blocks_res_0_nil in RES.
      eapply adl_fin_comb; [ | |exact RES|exact INV1]; lia.
    - rewrite (adl_blocks_res_0_cons _ _ (skipn_nonnil i0 ltac:(lia))) in RES.
      do 2 zstep. if_cases K1; zify_cond K1.
      +
        zstep.
        eapply (adl_tail_loop (Z.to_nat (n - i0)) i0 i0); [lia|lia|lia|lia| | |exact RES|exact INV1]; lia.
      + eapply adl_tail_setup; [ | | | | |exact RES|exact INV1]; lia.
  Qed.
End P.
