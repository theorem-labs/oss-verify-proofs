(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit CrcAGlue CrcA_zkit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= crcz_acc_hint.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : amem) (lo A : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 144.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis CKSH : ck_sh m.
  Hypothesis BUF : ck_buf RNG m A bs.
  Hypothesis A1 : 1 <= A.
  Hypothesis ALO : A + Z.of_nat (length bs) <= lo.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation LEN := (Z.of_nat (length bs)).
  Notation INV m1 := (crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs m m1).
  Notation POST res := (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m).

  Lemma crcz_ret : forall (m1 : amem) (res : Z)
      (x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    INV m1 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 res) x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x817bc) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 res x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           ([junk40 FR] & ST & MU & WM & MI & BY).
    pose_sp_range sp.
    do 15 zstep.
    release_frame FR ST (bv_unsigned sp). finish.
  Qed.

  Lemma crcz_epi : forall (m1 : amem) (c res : Z)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    INV m1 -> 0 <= c < 2^32 -> res = Z.lxor c M32 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 c))
          F (Z_to_bv 64 0x817b0) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 c res x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
           HINV Hc HR.
    zstep. zstep. zstep.
    setreg 10 (Z_to_bv 64 res) ltac:(rewrite HR; reflexivity).
    apply crcz_ret. exact HINV.
  Qed.

  Lemma crcz_bytes_loop : forall (k : nat) (m1 : amem) (i c res : Z)
      (x1 x5 x6 x7 x8 x9 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    INV m1 -> Z.of_nat (S k) = LEN - i -> 0 <= i -> 0 <= c < 2^32 ->
    res = Z.lxor (crc_bytes c (skipn (Z.to_nat i) bs)) M32 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (LEN - i)) x13 x14
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 c))
          F (Z_to_bv 64 0x8173c) fc None m1 (seg_rom asegs)).
  Proof.
    induction k as [|k IH];
      intros m1 i c res x1 x5 x6 x7 x8 x9 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 HINV Hk Hi Hc HR;
      pose proof HINV as (FRc & ST & MU & WM & MI & BY);
      pose proof BUF as (BY0 & BF & UNP & RB & RSH);
      pose proof KLO as KLO'; unfold KHIGH in KLO'; pose_sp_range sp;
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia);
      pose proof (bz_range bs i BF) as BR;
      set (idx := Z.land (Z.lxor (bz bs i) c) 255);
      pose proof (land255_range (Z.lxor (bz bs i) c)) as Hidx; fold idx in Hidx;
      pose proof (ctab_range idx) as CR;
      pose proof (ctab_shrng RNG RISH) as RSHT; unfold ACRCTAB in RSHT;
      rewrite (bz_skipn bs i) in HR by lia; rewrite crc_bytes_cons in HR;
      pose proof (crc_byte_range c (bz bs i) Hc) as CBR;
      destruct (unpoisoned_check_mu _ lo m m1 A (A + LEN) (A + i) 1 UNP MU WA
                  ltac:(lia) KLO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR);
      zstep; zstep; zstep; rewrite sxb_sval; zstep;
      ck_branch 14 0x8174c CK;
      pose proof (ck_buf_read m1 A bs i _ BY ltac:(lia) eq_refl) as RDB;
      zstep; cbv beta; rewrite (bz_val bs i BF);
      zstep; zstep; zstep; zstep;
      setreg 13 (Z_to_bv 64 (135264 + 4 * idx))
        ltac:(f_equal; subst idx; rewrite <- crc_idx_form by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia);
      destruct (tab_check_mu _ lo m m1 135264 256 idx (ctab_unpoisoned m CKSH) MU WA
                  ltac:(lia) KLO ltac:(reflexivity) Hidx) as (b2 & RD2 & CK2 & SR2);
      pose proof (ctab_read m1 idx (Z_to_bv 64 (135264 + 4 * idx)) MI Hidx eq_refl) as RDT;
      zstep; zstep; zstep; rewrite sxb_sval; zstep;
      ck_branch 17 0x81770 CK2;
      zstep; rewrite (zx32_lit (ctab idx)) by lia;
      zstep; zstep; zstep; zstep; zstep; zstep;
      change (Z.lxor (c ≫ 8) (ctab idx)) with (crc_byte c (bz bs i));
      if_cases KE; zify_cond KE.
    - exfalso. rewrite ?Z.mod_small in KE by lia. lia.
    - zstep. eapply crcz_epi; [exact HINV| exact CBR|].
      rewrite HR. replace (skipn (Z.to_nat (i + 1)) bs) with (@nil Z) by (symmetry; apply skipn_all2; lia). reflexivity.
    - replace (LEN - i + -1) with (LEN - (i + 1)) by lia. replace (A + i + 1) with (A + (i + 1)) by lia.
      eapply IH; [exact HINV| lia | lia | exact CBR | exact HR].
    - exfalso. rewrite ?Z.mod_small in KE by lia. lia.
  Qed.

  Lemma crcz_bytes : forall (m1 : amem) (i c res : Z)
      (x1 x5 x6 x7 x8 x9 x10 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    INV m1 -> 0 <= i <= LEN -> 0 <= c < 2^32 ->
    res = Z.lxor (crc_bytes c (skipn (Z.to_nat i) bs)) M32 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 x10 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (LEN - i)) x13 x14
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 c))
          F (Z_to_bv 64 0x81734) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 i c res x1 x5 x6 x7 x8 x9 x10 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 HINV Hi Hc HR.
    pose proof HINV as (FRc & ST & MU & WM & MI & BY). pose proof BUF as (BY0 & BF & UNP & RB & RSH).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    zstep. if_cases K; zify_cond K.
    - rewrite ?Z.mod_small in K by lia.
      eapply crcz_epi; [exact HINV| exact Hc|].
      rewrite HR. replace (skipn (Z.to_nat i) bs) with (@nil Z) by (symmetry; apply skipn_all2; lia). reflexivity.
    - rewrite ?Z.mod_small in K by lia. zstep.
      eapply (crcz_bytes_loop (Z.to_nat (LEN - i - 1))); [exact HINV| lia | lia | exact Hc | exact HR].
  Qed.
End P.
