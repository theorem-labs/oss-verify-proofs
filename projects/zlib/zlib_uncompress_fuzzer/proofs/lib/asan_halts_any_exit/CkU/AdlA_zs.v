(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel CkMathAdler CkWalk.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.CkU Require Import CkAImg CkATables CkAShadow CkAIface CkAKit AdlAGlue.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Definition adl_FRAMEC (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : amem) : Prop := exists junk,
  rw_cells asegs m1 (bv_unsigned sp + -160)
    [CB 56 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition adl_INVG (FRAME : amem -> Prop) (sp : word) (m : amem) (lo A : Z) (bs : list Z) (m1 : amem) : Prop :=
  FRAME m1 /\ stk asegs m1 lo (bv_unsigned sp + -160)
  /\ munch [(bv_unsigned sp - 160, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
  /\ bytes_at asegs m1 A (zb bs).

Lemma adl_W_above : forall sp : word, wabove [(bv_unsigned sp + -160, bv_unsigned sp)] (bv_unsigned sp - 160).
Proof. intros sp. cbn. split; [lia| exact I]. Qed.

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
  Notation INV := (adl_INVG FRAMEC sp m lo A bs).

  Notation W_above := (adl_W_above sp).

  Lemma adl_epi : forall res m1 (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    INV m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x95708) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros res m1 x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           ([junk FRM] & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    do 15 zstep.
    release_frame FRM ST (bv_unsigned sp).
    replace (SP + -160) with (SP - 160) in MU by lia.
    finish.
  Qed.

  Lemma bs_len1 : n = 1 -> bs = [bz bs 0].
  Proof using All.
    intros N1. destruct bs as [|x [|y l]]; cbn in NL; try lia. reflexivity.
  Qed.

  Lemma adl_len1 : forall m1 (x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    n = 1 -> INV m1 ->
    evtF asegs RNG (POST (adler32_z_model adler bs))
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 A) x12 x13 x14
               (Z_to_bv 64 (hi16 adler)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (lo16 adler)) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x94f20) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros m1 x1 x5 x6 x7 x8 x9 x10 x12 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 N1 INV1.
    pose proof INV1 as ([junk FRM] & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (lo16_range adler) as LR. pose proof (hi16_range adler) as HR.
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) A 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
    do 3 zstep. rewrite sxb_sval. zstep.
    ck_branch 12 0x94f30 CK.
    pose proof (ck_buf_read m1 A bs 0 _ BY ltac:(lia) eq_refl) as RDB. rewrite Z.add_0_r in RDB.
    pose proof (bz_range bs 0 BF) as BR.
    zstep. cbv beta. rewrite (bz_val bs 0 BF).
    do 10 zstep.
    setreg 10 (Z_to_bv 64 (csub (lo16 adler + bz bs 0))) ltac:(symmetry; apply csub_mach; lia).
    pose proof (csub_le (lo16 adler + bz bs 0) ltac:(lia)) as CL.
    do 7 zstep.
    setreg 11 (Z_to_bv 64 (csub (csub (lo16 adler + bz bs 0) + hi16 adler) * 2^16)) ltac:(symmetry; apply csub16_mach; lia).
    pose proof (csub_le (csub (lo16 adler + bz bs 0) + hi16 adler) ltac:(lia)) as CL2.
    zstep.
    setreg 10 (Z_to_bv 64 (adler32_z_model adler bs))
      ltac:(f_equal; rewrite (bs_len1 N1) at 1; rewrite <- (adler_len1_exit adler (bz bs 0) BR); reflexivity).
    zstep.
    apply adl_epi. exact INV1.
  Qed.

  Lemma adl_short_fin : forall sa sb res m1 (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    0 <= sa < 2^40 -> 0 <= sb < 2^50 ->
    res = Z.lor ((sb mod BASE) * 65536) (csub sa) ->
    INV m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 (Z_to_bv 64 sb) x16 (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x95368) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros sa sb res m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x16 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           SA SB RES INV1. pose proof INV1 as ([junk FRM] & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    pose_sp_range sp.
    do 10 zstep.
    setreg 11 (Z_to_bv 64 (csub sa)) ltac:(symmetry; apply csub_mach; lia).
    pose proof (csub_le sa ltac:(lia)) as CL.
    zstep.
    setreg 12 (Z_to_bv 64 (amag_t sb)) ltac:(f_equal; symmetry; apply amag_t_mach; lia).
    pose proof (amag_t_range sb ltac:(lia)) as TR. pose proof (amag_v_range sb ltac:(lia)) as VR.
    pose proof (amag_q_range sb ltac:(lia)) as QR. unfold amag_q in QR.
    do 7 zstep.
    setreg 15 (Z_to_bv 64 (sb mod 65521)) ltac:(f_equal; change 65521 with BASE at 1; rewrite <- (amag_mod sb) by lia; unfold amag_q; reflexivity).
    pose proof (mod_BASE_range sb) as MR. unfold BASE in MR.
    do 2 zstep.
    setreg 10 (Z_to_bv 64 res) ltac:(f_equal; rewrite RES; unfold BASE; rewrite Z.shiftl_mul_pow2 by lia;
                                     change (2 ^ 16) with 65536; rewrite (Z.mod_small (sb mod 65521 * 65536)) by lia; reflexivity).
    zstep.
    apply adl_epi. exact INV1.
  Qed.

  Lemma adl_short_loop : forall (k : nat) i sa sb res m1
      (x1 x5 x6 x7 x8 x9 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    Z.of_nat k = n - i -> 0 <= i -> 1 <= n - i -> n < 16 ->
    0 <= sa <= 65535 + 255 * i -> 0 <= sb <= 65535 + 70000 * i ->
    res = Z.lor ((snd (adler_fold (sa, sb) (skipn (Z.to_nat i) bs)) mod BASE) * 65536)
                (csub (fst (adler_fold (sa, sb) (skipn (Z.to_nat i) bs)))) ->
    INV m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -160)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (n - i)) x13 x14
               (Z_to_bv 64 sb) (Z_to_bv 64 2147450880) (Z_to_bv 64 sa) x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x94f94) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction k as [|k IH]; intros i sa sb res m1 x1 x5 x6 x7 x8 x9 x13 x14 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
                                   HK I0 IN N16 SA SB RES INV1; [lia|].
    pose proof INV1 as ([junk FRM] & ST & MU & WM & MI & BY).
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    destruct (unpoisoned_check_mu W (SP - 160) m m1 A (A + n) (A + i) 1 UNP MU W_above
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
    do 3 zstep. rewrite sxb_sval. zstep.
    ck_branch 14 0x94fa4 CK.
    pose proof (ck_buf_read m1 A bs i _ BY ltac:(lia) eq_refl) as RDB.
    pose proof (bz_range bs i BF) as BR.
    zstep. cbv beta. rewrite (bz_val bs i BF).
    do 6 zstep.
    rewrite (bz_skipn bs i ltac:(lia)) in RES. rewrite adler_fold_cons in RES.
    replace (sb + (sa + bz bs i)) with (sa + bz bs i + sb) in RES by lia.
    if_cases KB; zify_cond KB.
    -
      replace (A + i + 1) with (A + (i + 1)) by lia. replace (n - i + -1) with (n - (i + 1)) by lia.
      eapply (IH (i + 1)); [lia|lia|lia|lia| | |exact RES|exact INV1]; lia.
    -
      zstep.
      replace (Z.to_nat (i + 1)) with (length bs) in RES by lia. rewrite skipn_all in RES. cbn [adler_fold fst snd] in RES.
      eapply adl_short_fin; [ | | exact RES | exact INV1]; lia.
  Qed.
End P.

