(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk CkHarness.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit FuzzAGlue AdlA_closed FuzzA_a FuzzA_b FuzzA_c.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (D n : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 272.
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
  Notation W := [(SP - 272, SP)].
  Notation POST res := (ck_postA 272 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation INV := (fz_INV sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs).
  Notation CTXA L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo D n bs
                        LOS KLO D1 NL DLO BF UNP RB RS CKSH RI RISH RSTK).
  Notation CTXC L := (L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo D n bs
                        LOS KLO D1 NL DLO BF UNP RB RS CKSH RI RISH RSTK NR CRC32Z CRC32 CRC32N COMB GEN OP).

  Local Ltac fz_reinv I :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (I : INV mx) by (split; [eexists; eassumption|]; repeat (split; [assumption|]); assumption) end.

  Lemma fz_loop1 : forall (k : nat) off q bsz m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x27 x28 x29 x30 x31 : word),
    Z.of_nat k > n - off -> 1 <= bsz <= 255 -> 0 <= q -> off = bsz * q -> off <= n -> INV m1 ->
    evtF asegs RNG (POST 0)
      (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 (Z_to_bv 64 n) (Z_to_bv 64 D) x10 x11
               x12 x13 x14 x15 x16 x17 (Z_to_bv 64 1) (Z_to_bv 64 n) (Z_to_bv 64 bsz) (Z_to_bv 64 (crc32_combine_gen bsz)) (Z_to_bv 64 0)
               (Z_to_bv 64 (crc32_spec 0 (fz_pre bs off))) x24 (Z_to_bv 64 off) (Z_to_bv 64 4294967295) x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x805e0) fc None m1 (seg_rom asegs)).
  Proof using All.
    induction k as [|k IH]; intros off q bsz m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x27 x28 x29 x30 x31
                                   HK BZ Q0 OQ OL INV1.
    { exfalso. lia. }
    pose proof (crc32_combine_gen_range bsz) as OPR. pose proof (crc32_combine_gen_nz bsz ltac:(lia)) as NZ1.
    remember (crc32_combine_gen bsz) as OPG eqn:EOPG in *.
    pose proof INV1 as ([junk FRM] & ST & MU & WM & MI & BY & GOT & SHB).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    assert (OFF0 : 0 <= off) by nia.
    pose proof (fz_crc_range bs off BF) as CR0.
    do 2 zstep.
    setreg 25 (Z_to_bv 64 (off + bsz)) ltac:(f_equal; symmetry; apply swrap32_small; lia).
    do 2 zstep.
    setreg 10 (Z_to_bv 64 off) ltac:(f_equal; symmetry; apply Z.mod_small; lia).
    zstep.
    if_cases KX; zify_cond KX.
    {
      eapply (CTXC fz_mid off q bsz); [lia|lia|lia|lia|lia|exact INV1]. }
    pose proof (CTXA fz_bufZ m1 off bsz INV1 ltac:(lia) ltac:(lia) ltac:(lia)) as BUF1.
    pose proof (CTXA fz_cksh m1 INV1) as SH1.
    do 5 zstep.
    call_sp (CRC32Z_u CRC32Z RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 0 (D + off) (fz_chunk bs off bsz));
      [exact MI| exact ST| lia| exact KLO| exact GOT| exact SHB| exact SH1| reflexivity| lia| reflexivity| lia
      | rewrite fz_chunk_length by lia; lia | f_equal; symmetry; apply fz_chunk_length; lia | exact BUF1
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV1 BUF1 SH1. fz_reinv INV2. pose proof (CTXA fz_cksh _ INV2) as SH2.
    pose proof (CTXA fz_bufZ _ off bsz INV2 ltac:(lia) ltac:(lia) ltac:(lia)) as BUF2.
    pose proof (crc32_z_model_range (D + off) 0 (fz_chunk bs off bsz) (fz_chunk_bytes bs off bsz BF)) as C3R.
    assert (E4 : crc32_combine_op (crc32_spec 0 (fz_pre bs off)) (crc32_z_model (D + off) 0 (fz_chunk bs off bsz)) OPG
                 = crc32_spec 0 (fz_pre bs (off + bsz))).
    { rewrite EOPG. rewrite <- (fz_assert1 (D + off) (D + off) bs off bsz BF ltac:(lia) ltac:(lia) ltac:(lia)).
      apply fz_crc_step; [exact BF| lia| lia]. }
    pose proof (fz_crc_range bs (off + bsz) BF) as CR1.
    set (CRC3 := crc32_z_model (D + off) 0 (fz_chunk bs off bsz)) in *.
    zstep.
    setreg 11 (Z_to_bv 64 CRC3) ltac:(f_equal; symmetry; apply land_M32_small; lia).
    do 3 zstep.
    leafcall (OP RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (crc32_spec 0 (fz_pre bs off)) CRC3 OPG); [reflexivity| reflexivity| reflexivity| lia| lia| lia| exact NZ1| ].
    rewrite E4.
    do 2 zstep.
    setreg 27 (Z_to_bv 64 (crc32_spec 0 (fz_pre bs (off + bsz)))) ltac:(f_equal; symmetry; apply Z.mod_small; lia).
    do 4 zstep.
    call_sp (CRC32Z_u CRC32Z RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (crc32_spec 0 (fz_pre bs off)) (D + off) (fz_chunk bs off bsz));
      [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| exact SH2| reflexivity| lia| reflexivity| lia
      | rewrite fz_chunk_length by lia; lia | f_equal; symmetry; apply fz_chunk_length; lia | exact BUF2
      | eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV2 BUF2 SH2. fz_reinv INV3.
    rewrite (fz_crc_step (D + off) bs off bsz BF ltac:(lia) ltac:(lia)).
    do 2 zstep.
    setreg 10 (Z_to_bv 64 (crc32_spec 0 (fz_pre bs (off + bsz)))) ltac:(f_equal; symmetry; apply Z.mod_small; lia).
    do 2 zstep.
    if_true.
    subst OPG.
    eapply (IH (off + bsz) (q + 1) bsz); [lia|lia|lia|lia|lia|exact INV3].
  Qed.

  Lemma fz_entry : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv asegs m -> stk asegs m lo SP -> rt_got m -> rt_shbase m -> bytes_at asegs m D (zb bs) ->
    evtF asegs RNG (POST 0)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          FR (Z_to_bv 64 0x80514) fc None m (seg_rom asegs)).
  Proof using All.
    intros t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI ST GOT SHB BY.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    carve_frame 112%nat ST.
    do 14 zstep.
    do 9 zstep.
    call_sp (CRC32N_u CRC32N RNG); [exact MI| exact ST| lia| exact KLO| reflexivity| eapply rng_sub'; [exact RSTK| lia] | ].
    do 5 zstep.
    call_sp (ADLN_u RNG); [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| reflexivity| reflexivity| eapply rng_sub'; [exact RSTK| lia] | ].
    do 4 zstep.
    if_cases KS; zify_cond KS. { exfalso. Z.div_mod_to_equations. lia. }
    clear KS.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      destruct (unpoisoned_check_mu W (SP - 272) m mx D (D + n) D 1 UNP MU (fz_W_above sp)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR);
      pose proof (ck_buf_read mx D bs 0 _ BY ltac:(lia) eq_refl) as RDB
    end.
    rewrite Z.add_0_r in RDB.
    pose proof (bz_range bs 0 BF) as BR.
    do 4 zstep. rewrite sxb_sval. zstep.
    ck_branch 11 0x805a8 CK. clear RD CK SR.
    zstep. zstep. cbv beta. rewrite (bz_val bs 0 BF). clear RDB.
    do 5 zstep.
    set (bsz := bz bs 0 + Z.b2z (bz bs 0 <? 1)) in *.
    assert (BZ : 1 <= bsz <= 255) by (subst bsz; destruct (Z.ltb_spec (bz bs 0) 1); cbn [Z.b2z]; lia).
    fz_reinv INV1. pose proof (CTXA fz_cksh _ INV1) as SH1.
    do 2 zstep.
    call_sp (GEN_u GEN RNG _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bsz);
      [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| exact SH1| reflexivity| lia| eapply rng_sub'; [exact RSTK| lia] | ].
    clear INV1 SH1. fz_reinv INV2.
    pose proof (crc32_combine_gen_range bsz) as OPR.
    remember (crc32_combine_gen bsz) as OPG eqn:EOPG in *.
    do 3 zstep.
    setreg 21 (Z_to_bv 64 OPG) ltac:(f_equal; symmetry; apply Z.mod_small; lia).
    zstep.
    setreg 19 (Z_to_bv 64 n) ltac:(f_equal; rewrite Z.add_0_r; symmetry; apply swrap32_small; lia).
    zstep.
    subst OPG.
    pose proof (fz_loop1 (Z.to_nat (n + 1)) 0 0 bsz) as HL. rewrite fz_pre_0, harness_crc_init in HL.
    eapply HL; [lia|lia|lia|lia|lia|exact INV2].
  Qed.
End P.

Lemma fz_early : crc32_null_stmtA ->
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (Dreg nreg : Z),
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 272 -> KHIGH <= lo ->
  rt_got m -> rt_shbase m -> ck_sh m -> 0 <= nreg < 2^64 -> ~ (1 <= nreg <= 2^20) ->
  rng_aimg RNG -> rng_aimg_sh RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (ck_postA 272 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc 0 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dreg) (Z_to_bv 64 nreg) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 0x80514) fc None m (seg_rom asegs)).
Proof.
  intros CRC32N RNG ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m lo Dreg nreg
         MI ST LOS KLO GOT SHB CKSH NRR NOUT RI RISH RSTK.
  pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
  pose proof (munch_refl [(bv_unsigned sp - 272, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (UNP0 : unpoisoned m lo (lo + 0)) by (replace (lo + 0) with lo by lia; apply unpoisoned_nil; lia).
  assert (RB0 : rng RNG lo 0) by (eapply rng_sub'; [exact RSTK| lia]).
  assert (RS0 : shrng RNG lo (lo + 0)) by (intros H; lia).
  carve_frame 112%nat ST.
  do 14 zstep.
  do 9 zstep.
  call_sp (CRC32N_u CRC32N RNG); [exact MI| exact ST| lia| exact KLO| reflexivity| eapply rng_sub'; [exact RSTK| lia] | ].
  do 5 zstep.
  call_sp (ADLN_u RNG); [eassumption| eassumption| lia| exact KLO| eassumption| eassumption| reflexivity| reflexivity| eapply rng_sub'; [exact RSTK| lia] | ].
  do 4 zstep.
  if_cases KS; zify_cond KS. 2:{ exfalso. Z.div_mod_to_equations. lia. }
  eapply (fz_epi RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo lo 0 []
                 LOS KLO ltac:(lia) eq_refl ltac:(lia) (Forall_nil _) UNP0 RB0 RS0 CKSH RI RISH RSTK).
  split; [eexists; eassumption|]. do 4 (split; [assumption|]). split; [apply bytes_at_nil; lia|]. split; assumption.
Qed.

Theorem ck_fuzz_proofA :
  crc32_z_stmtA -> crc32_stmtA -> crc32_null_stmtA -> crc32_combine_stmtA -> crc32_combine_gen_stmtA -> crc32_combine_op_stmtA ->
  ck_fuzz_stmtA.
Proof.
  intros CRC32Z CRC32 CRC32N COMB GEN OP.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m lo D n MI ST LOS KLO GOT SHB CKSH A0 A1 NRR BUF RI RISH RSTK.
  subst a0 a1. unfold CK_FUZZ_STACK in *. unfold ACK_FUZZ.
  destruct (Z_le_dec 1 n) as [L1|L1]; [destruct (Z_le_dec n (2^20)) as [L2|L2]|].
  - destruct (BUF (conj L1 L2)) as (bs & NL & (BY & BF & UNP & RB & RS) & D1 & DLO).
    rewrite NL in UNP, RB, RS.
    eapply (fz_entry RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc m lo D n bs
                     LOS KLO D1 NL DLO BF UNP RB RS CKSH RI RISH RSTK (conj L1 L2) CRC32Z CRC32 CRC32N COMB GEN OP); assumption.
  - eapply (fz_early CRC32N); try eassumption. lia.
  - eapply (fz_early CRC32N); try eassumption. lia.
Qed.
