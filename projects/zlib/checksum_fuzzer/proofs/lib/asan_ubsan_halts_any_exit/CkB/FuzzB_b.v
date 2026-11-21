(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk CkHarness.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkA Require Import FuzzAGlue.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit AdlB_closed FuzzB_a.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (D n : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 288.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis D1 : 1 <= D.
  Hypothesis NL : Z.of_nat (length bs) = n.
  Hypothesis DLO : D + n <= lo.
  Hypothesis BF : Forall (fun b => 0 <= b < 256) bs.
  Hypothesis UNP : unpoisoned m D (D + n).
  Hypothesis RB : rng RNG D n.
  Hypothesis RS : shrng RNG D (D + n).
  Hypothesis CKSH : ck_sh m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).
  Hypothesis NR : 1 <= n <= 2^20.

  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 288, SP)].
  Notation POST res := (ck_postA 288 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation INV := (fz_INV sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs).
  Notation INV1 := (fz_INV1 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs).
  Notation TO0 I := (fz_INV1_0 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs _ I).
  Notation CTXA L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo D n bs
                        LOS KLO D1 NL DLO BF UNP RB RS CKSH RI RISH RSTK).

  Local Ltac fz_reinv I :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I : INV1 mx) by (split; [eassumption|]; repeat (split; [assumption|]); assumption) end.

  Lemma fz_adler_tail : forall off m1 (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 x31 : word),
    0 <= off <= n -> n - off < 2^29 -> INV1 m1 ->
    evtF asegs RNG (POST 0)
      (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 (adler_spec 1 (fz_pre bs off))) (Z_to_bv 64 off)
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) x20 (Z_to_bv 64 (n - off)) x22 x23 x24 x25 (Z_to_bv 64 4294967295) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x80714) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros off m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x20 x22 x23 x24 x25 x27 x28 x29 x30 x31 OFF RL INV1.
    pose proof INV1 as (FRM & ST & MU & WM & MI & BY & GOT & SHB). unfold fz_FRAME1 in FRM.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    pose proof (fz_adler_range bs off) as AR0.
    pose proof (CTXA fz_bufZ m1 off (n - off) (TO0 INV1) ltac:(lia) ltac:(lia) ltac:(lia)) as BUF1.
    do 2 zstep.
    setreg 10 (Z_to_bv 64 (adler_spec 1 (fz_pre bs off))) ltac:(f_equal; symmetry; apply land_M32_small; lia).
    do 2 zstep.
    call_sp (ADLZ_u RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (adler_spec 1 (fz_pre bs off)) (D + off) (fz_chunk bs off (n - off)));
      [exact MI| exact ST| lia| exact KLO| exact GOT| exact SHB| reflexivity| lia| reflexivity| lia
      | rewrite fz_chunk_length by lia; lia | f_equal; symmetry; apply fz_chunk_length; lia | exact BUF1
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV1 BUF1. fz_reinv INV2.
    rewrite (fz_adler_step bs off (n - off) BF ltac:(lia) ltac:(lia)).
    replace (off + (n - off)) with n by lia. rewrite (fz_pre_all bs n ltac:(lia)).
    pose proof (adler_spec_1_range bs) as ADR. set (AD := adler_spec 1 bs) in *.
    pose proof (CTXA fz_buf_whole _ (TO0 INV2)) as BUFW.
    do 7 zstep.
    call_sp (ADL_u RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 D n bs);
      [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| reflexivity| lia| reflexivity| lia| lia
      | reflexivity | lia | rewrite Z.mod_small by lia; lia | exact BUFW
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV2 BUFW. fz_reinv INV3.
    rewrite (fz_adler_whole bs BF). fold AD.
    do 2 zstep. if_false.
    do 2 zstep.
    setreg 9 (Z_to_bv 64 AD) ltac:(f_equal; symmetry; apply land_M32_small; lia).
    do 3 zstep.
    leafcall (adler32_combine_A RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AD AD n); [eassumption| reflexivity| reflexivity| reflexivity| lia| lia| lia| exact RI| ].
    do 5 zstep.
    leafcall (adler32_combine_A RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AD AD n); [eassumption| reflexivity| reflexivity| reflexivity| lia| lia| lia| exact RI| ].
    zstep. if_false.
    eapply (CTXA fz_epi). exact (TO0 INV3).
  Qed.

  Lemma fz_loop2 : forall (k : nat) off q bsz m1 (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x28 x29 x30 x31 : word),
    Z.of_nat k >= n - off -> 1 <= bsz <= 255 -> 0 <= q -> off = bsz * q -> off + bsz <= n -> INV1 m1 ->
    evtF asegs RNG (POST 0)
      (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 (adler_spec 1 (fz_pre bs off))) x11
               x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) (Z_to_bv 64 bsz) (Z_to_bv 64 (n mod bsz)) (Z_to_bv 64 off) x23 x24 x25
               (Z_to_bv 64 4294967295) (Z_to_bv 64 (18446744073709551615 - D)) x28 x29 x30 x31)
          FR (Z_to_bv 64 0x806e0) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction k as [|k IH]; intros off q bsz m1 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x23 x24 x25 x28 x29 x30 x31
                                   HK BZ Q0 OQ OB INV1; [lia|].
    pose proof INV1 as (FRM & ST & MU & WM & MI & BY & GOT & SHB). unfold fz_FRAME1 in FRM.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    assert (OFF0 : 0 <= off) by nia.
    pose proof (fz_adler_range bs off) as AR0.
    pose proof (CTXA fz_bufZ m1 off bsz (TO0 INV1) ltac:(lia) ltac:(lia) ltac:(lia)) as BUF1.
    do 2 zstep.
    setreg 11 (Z_to_bv 64 off) ltac:(f_equal; symmetry; apply Z.mod_small; lia).
    zstep. if_cases KT; zify_cond KT; [exfalso; lia|]. clear KT.
    do 2 zstep.
    setreg 10 (Z_to_bv 64 (adler_spec 1 (fz_pre bs off))) ltac:(f_equal; symmetry; apply land_M32_small; lia).
    do 2 zstep.
    call_sp (ADLZ_u RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (adler_spec 1 (fz_pre bs off)) (D + off) (fz_chunk bs off bsz));
      [exact MI| exact ST| lia| exact KLO| exact GOT| exact SHB| reflexivity| lia| reflexivity| lia
      | rewrite fz_chunk_length by lia; lia | f_equal; symmetry; apply fz_chunk_length; lia | exact BUF1
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV1 BUF1. fz_reinv INV2.
    rewrite (fz_adler_step bs off bsz BF ltac:(lia) ltac:(lia)).
    do 2 zstep.
    setreg 11 (Z_to_bv 64 (bsz + (off + bsz))) ltac:(f_equal; symmetry; apply swrap32_small; lia).
    zstep.
    if_cases KL; zify_cond KL.
    -
      eapply (IH (off + bsz) (q + 1) bsz); [lia|lia|lia|lia|lia|exact INV2].
    -
      do 2 zstep.
      setreg 11 (Z_to_bv 64 (off + bsz)) ltac:(f_equal; symmetry; apply Z.mod_small; lia).
      zstep. if_cases KT; zify_cond KT; [exfalso; lia|]. clear KT.
      replace (n mod bsz) with (n - (off + bsz)) by (symmetry; apply (fz_tail_len n bsz (q + 1) (off + bsz)); lia).
      eapply fz_adler_tail; [lia|lia|exact INV2].
  Qed.
End P.
