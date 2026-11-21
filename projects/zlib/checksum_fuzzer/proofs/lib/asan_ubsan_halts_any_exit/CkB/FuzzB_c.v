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
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit AdlB_closed FuzzB_a FuzzB_b.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Lemma remu_mach : forall a b, 0 <= a < 2^64 -> 0 < b < 2^64 ->
  mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
  intros a b Ha Hb. unfold mul_div.
  assert (EB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
  assert (EA : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  rewrite EB. destruct (Z.eqb_spec b 0); [lia|].
  apply bv_eq. rewrite bv_modu_unsigned, EA, EB.
  rewrite unsigned_lit; [reflexivity|]. pose proof (Z.mod_pos_bound a b ltac:(lia)). lia.
Qed.

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
  Hypothesis CRC32Z : crc32_z_stmtA.
  Hypothesis CRC32 : crc32_stmtA.
  Hypothesis CRC32N : crc32_null_stmtA.
  Hypothesis COMB : crc32_combine_stmtA.
  Hypothesis GEN : crc32_combine_gen_stmtA.
  Hypothesis OP : crc32_combine_op_stmtA.

  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 288, SP)].
  Notation POST res := (ck_postA 288 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation INV := (fz_INV sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs).
  Notation INV1 := (fz_INV1 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs).
  Notation TO0 I := (fz_INV1_0 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs _ I).
  Notation CTXA L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo D n bs
                        LOS KLO D1 NL DLO BF UNP RB RS CKSH RI RISH RSTK).
  Notation CTXB L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo D n bs
                        LOS KLO D1 NL DLO BF UNP RB RS CKSH RI RISH RSTK NR).

  Local Ltac fz_reinv I :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I : INV1 mx) by (split; [eassumption|]; repeat (split; [assumption|]); assumption) end.

  Lemma fz_mid : forall off q bsz m1 (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 : word),
    1 <= bsz <= 255 -> 0 <= q -> off = bsz * q -> off <= n -> n < off + bsz -> INV1 m1 ->
    evtF asegs RNG (POST 0)
      (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D) x10 (Z_to_bv 64 off)
               x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (crc32_spec 0 (fz_pre bs off))) (Z_to_bv 64 n) (Z_to_bv 64 bsz) x21 (Z_to_bv 64 0)
               x23 x24 x25 (Z_to_bv 64 4294967295) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x80600) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros off q bsz m1 x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x21 x23 x24 x25 x27 x28 x29 x30 x31 BZ Q0 OQ OL OH INV1.
    pose proof INV1 as (FRM & ST & MU & WM & MI & BY & GOT & SHB). unfold fz_FRAME1 in FRM.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    assert (OFF0 : 0 <= off) by nia.
    pose proof (fz_crc_range bs off BF) as CR0.
    pose proof (CTXA fz_bufZ m1 off (n - off) (TO0 INV1) ltac:(lia) ltac:(lia) ltac:(lia)) as BUF1.
    pose proof (CTXA fz_cksh m1 (TO0 INV1)) as SH1.
    assert (TL : n mod bsz = n - off) by (apply (fz_tail_len n bsz q off); lia).
    zstep.
    setreg 27 (Z_to_bv 64 (18446744073709551615 - D)) ltac:(first [reflexivity | f_equal; symmetry; apply zb_lxor_ones; lia]).
    zstep. if_cases KT; zify_cond KT; [exfalso; lia|]. clear KT.
    do 2 zstep.
    rewrite (remu_mach n bsz ltac:(lia) ltac:(lia)).
    do 3 zstep.
    call_sp (CRC32Z_u CRC32Z RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (crc32_spec 0 (fz_pre bs off)) (D + off) (fz_chunk bs off (n - off)));
      [exact MI| exact ST| lia| exact KLO| exact GOT| exact SHB| exact SH1| reflexivity| lia| reflexivity| lia
      | rewrite fz_chunk_length by lia; lia | f_equal; rewrite fz_chunk_length by lia; exact TL | exact BUF1
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV1 BUF1 SH1. fz_reinv INV2. pose proof (CTXA fz_cksh _ (TO0 INV2)) as SH2.
    rewrite (fz_crc_step (D + off) bs off (n - off) BF ltac:(lia) ltac:(lia)).
    replace (off + (n - off)) with n by lia. rewrite (fz_pre_all bs n ltac:(lia)).
    pose proof (crc32_spec_range 0 bs BF) as CRR. set (CRC := crc32_spec 0 bs) in *.
    pose proof (CTXA fz_buf_whole _ (TO0 INV2)) as BUFW.
    do 6 zstep.
    call_sp (CRC32_u CRC32 RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 D n bs);
      [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| exact SH2| reflexivity| lia| reflexivity| lia| lia
      | reflexivity | lia | rewrite Z.mod_small by lia; lia | exact BUFW
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV2 BUFW SH2. fz_reinv INV3. pose proof (CTXA fz_cksh _ (TO0 INV3)) as SH3.
    rewrite (fz_crc_whole D bs BF). fold CRC.
    do 2 zstep. if_false.
    do 2 zstep.
    setreg 22 (Z_to_bv 64 CRC) ltac:(f_equal; symmetry; apply land_M32_small; lia).
    do 4 zstep.
    call_sp (COMB_u COMB RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRC CRC n); [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| eassumption| reflexivity| reflexivity| reflexivity| lia| lia| lia| eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV3 SH3. fz_reinv INV4. pose proof (CTXA fz_cksh _ (TO0 INV4)) as SH4.
    do 5 zstep.
    call_sp (COMB_u COMB RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRC CRC n); [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| eassumption| reflexivity| reflexivity| reflexivity| lia| lia| lia| eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV4 SH4. fz_reinv INV5. pose proof (CTXA fz_cksh _ (TO0 INV5)) as SH5.
    zstep. if_false.
    do 2 zstep.
    call_sp (GEN_u GEN RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ n);
      [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| eassumption| reflexivity| lia| eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV5 SH5. fz_reinv INV6. pose proof (CTXA fz_cksh _ (TO0 INV6)) as SH6.
    pose proof (crc32_combine_gen_range n) as OPR. pose proof (crc32_combine_gen_nz n ltac:(lia)) as NZ2.
    set (OP2 := crc32_combine_gen n) in *. assert (EOP2 : OP2 = crc32_combine_gen n) by reflexivity. clearbody OP2.
    zstep.
    setreg 24 (Z_to_bv 64 OP2) ltac:(f_equal; symmetry; apply land_M32_small; lia).
    do 4 zstep.
    leafcall (OP RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRC CRC OP2); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact NZ2| ].
    do 5 zstep.
    leafcall (OP RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRC CRC OP2); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact NZ2| ].
    zstep. if_false.
    do 4 zstep.
    call_sp (COMB_u COMB RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRC CRC n); [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| eassumption| reflexivity| reflexivity| reflexivity| lia| lia| lia| eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV6 SH6. fz_reinv INV7.
    rewrite (harness_assert5 CRC CRC n eq_refl). rewrite <- EOP2.
    do 5 zstep.
    leafcall (OP RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CRC CRC OP2); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact NZ2| ].
    zstep. if_false.
    zstep.
    if_cases KB; zify_cond KB.
    -
      do 2 zstep.
      pose proof (CTXB fz_loop2 (Z.to_nat n) 0 0 bsz) as HL. rewrite fz_pre_0, harness_adler_init in HL.
      eapply HL; [lia|lia|lia|lia|lia|exact INV7].
    -
      do 3 zstep.
      pose proof (CTXB fz_adler_tail 0) as HT. rewrite fz_pre_0, harness_adler_init, Z.sub_0_r in HT.
      replace (n mod bsz) with n by (symmetry; apply Z.mod_small; lia).
      eapply HT; [lia|lia|exact INV7].
  Qed.
End P.
