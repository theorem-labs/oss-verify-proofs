(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit CrcAGlue CrcAMirror CrcA_zkit CrcA_zkit2 CrcA_zbloop.
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
  Hypothesis TAIL : crcz_tail_stmt RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs.
  Hypothesis LAST : crcz_last_stmt RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs.

  Notation SP := (bv_unsigned sp).
  Notation LEN := (Z.of_nat (length bs)).
  Notation INV m1 := (crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs m m1).
  Notation POST res := (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m).

  Lemma crcz_blk : forall (m1 : amem) (i c res : Z)
      (x1 x5 x6 x8 x9 x10 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    INV m1 -> 0 <= i -> (A + i) mod 4 = 0 -> 20 <= LEN - i -> 0 <= c < 2^32 ->
    res = (let r := braid_from c (skipn (Z.to_nat i) bs) in Z.lxor (crc_bytes (fst r) (snd r)) M32) ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 (LEN - i)) x8 x9 x10 (Z_to_bv 64 (A + i)) x12 x13 x14
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 c))
          F (Z_to_bv 64 0x80a54) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 i c res x1 x5 x6 x8 x9 x10 x12 x13 x14 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
           HINV Hi Hal Hn Hc HR.
    pose proof HINV as ([junk40 FR] & ST & MU & WM & MI & BY).
    pose proof BUF as (BY0 & BF & UNP & RB & RSH).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
    pose_zr_lits. pose proof (zb_length bs) as ZBL.
    remember (LEN - i) as n1 eqn:En.
    assert (Rn : 0 <= n1 < 2 ^ 64) by lia.
    pose proof (mulhu20_range n1 Rn) as RQ. pose proof (div20_form n1 Rn) as DQ.
    remember (n1 * 14757395258967641293 / 18446744073709551616) as Q eqn:EQ.
    remember (n1 / 20) as blks eqn:Eb.
    assert (RB20 : 0 <= blks < 2 ^ 64) by (rewrite Eb; Z.div_mod_to_equations; lia).
    assert (B1 : 1 <= blks) by (rewrite Eb; Z.div_mod_to_equations; lia).
    assert (BL : i + 20 * blks <= LEN) by (rewrite Eb; Z.div_mod_to_equations; lia).
    assert (Ebl : blks = (LEN - i) / 20) by (rewrite Eb, En; reflexivity).
    zstep. zstep. zstep. zstep.
    zstep. rewrite mulhu20_form, <- EQ.
    zstep. rewrite DQ.
    zstep. zstep. if_cases K; zify_cond K.
    -
      assert (BK : blks = 1) by (rewrite ?Z.mod_small in K by lia; lia).
      zstep. zstep. zstep. zstep.
      destruct (unpoisoned_check_mu _ lo m m1 A (A + LEN) (A + i) 4 UNP MU WA ALO KLO
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR).
      assert (AR : 0 <= A + i < 2 ^ 64) by lia.
      zstep. zstep. zstep. rewrite sxb_sval. zstep. ck_fast 12 0x81054 CK.
      eapply (LAST m1 i c 0 0 0 0 n1 blks res); try eassumption; try lia.
      rewrite HR. cbv zeta.
      rewrite (braid_from_lanes c bs i blks c 0 0 0 0 Hi Ebl B1 BL).
      + cbn [fst snd]. rewrite BK. replace (i + 20 * (1 - 1)) with i by lia. reflexivity.
      + rewrite BK. cbn [Z.sub Z.to_nat Z.pos_sub Z.add Z.opp]. rewrite braid_state_0, (Z.mod_small c), !Z.mod_0_l by lia. reflexivity.
    -
      assert (BK : 2 <= blks) by (rewrite ?Z.mod_small in K by lia; lia).
      assert (RM : 0 <= blks * 20 < 2 ^ 64) by lia.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        lazymatch goal with H : rw_cells asegs mx (SP + -144) (CB 8 ?j :: C8 ?a :: C8 ?b :: C8 ?c0 :: CB 8 ?j2 :: ?rest) |- _ =>
          apply (rw_cells_CB8_C8 mx (SP + -144) [CB 8 j; C8 a; C8 b; C8 c0] j2 rest) in H; cbn [app] in H
        end end.
      setreg 6 (Z_to_bv 64 (blks - 1)) ltac:(f_equal; lia).
      eapply evtF_cut.
      { eapply (braid_loop RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs LOS KLO CKSH BUF A1 ALO RI RISH RSTK)
          with (i0 := i) (k := Z.to_nat (blks - 2)) (c := c) (nb := blks - 1) (t := 0) (ib := i) (cnt := blks - 1) (x0 := c) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0);
          try lia.
        - split; [eexists; eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; eassumption.
        - cbn [Z.to_nat]. rewrite braid_state_0, (Z.mod_small c), !Z.mod_0_l by lia. reflexivity. }
      cbv beta. intros ms3 P3. unfold bloop_post in P3. destruct_exs P3.
      destruct P3 as (-> & HINV3 & (RX0 & RX1 & RX2 & RX3 & RX4) & EL).
      pose proof HINV3 as ([j8 FR3] & ST3 & MU3 & WM3 & MI3 & BY3).
      zstep. zstep. zstep.
      setreg 11 (Z_to_bv 64 (A + (i + 20 * (blks - 1)))) ltac:(f_equal; lia).
      zstep. zstep.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
        destruct (unpoisoned_check_mu _ lo m mx A (A + LEN) (A + (i + 20 * (blks - 1))) 4 UNP MU3 WA ALO KLO
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR) end.
      assert (AR : 0 <= A + (i + 20 * (blks - 1)) < 2 ^ 64) by lia.
      zstep. zstep. zstep. rewrite sxb_sval. zstep. ck_fast_z 12 0x81054 CK.
      eapply (LAST _ (i + 20 * (blks - 1)) _ _ _ _ _ n1 blks res); try eassumption; try lia.
      all: first [ (eapply crcz_invb_inv; exact HINV3)
                 | (rewrite HR; cbv zeta; rewrite (braid_from_lanes c bs i blks _ _ _ _ _ Hi Ebl B1 BL EL); reflexivity)
                 | (Z.div_mod_to_equations; lia) ].
  Qed.

  Lemma crcz_align : forall (k : nat) (m1 : amem) (i c res : Z)
      (x1 x5 x6 x7 x8 x9 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 : word),
    INV m1 -> 0 <= i -> Z.of_nat (S k) = 4 - (A + i) mod 4 -> (A + i) mod 4 <> 0 ->
    i + (4 - (A + i) mod 4) + 20 <= LEN -> 0 <= c < 2^32 ->
    res = crcz_from A c bs i ->
    evtF asegs RNG (POST res)
      (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (A + i)) (Z_to_bv 64 (LEN - i)) x13 (Z_to_bv 64 1)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 c))
          F (Z_to_bv 64 0x809c8) fc None m1 (seg_rom asegs)).
  Proof.
    induction k as [|k IH];
      intros m1 i c res x1 x5 x6 x7 x8 x9 x13 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 HINV Hi Hk Hna Hl Hc HR;
      pose proof HINV as (FRc & ST & MU & WM & MI & BY);
      pose proof BUF as (BY0 & BF & UNP & RB & RSH);
      pose proof KLO as KLO'; unfold KHIGH in KLO'; pose_sp_range sp;
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia);
      pose proof (ctab_shrng RNG RISH) as RSHT; unfold ACRCTAB in RSHT;
      pose_zr_lits;
      pose proof (bz_range bs i BF) as BR;
      assert (TL : 135264 + 4 * 256 <= lo) by lia;
      rewrite (crcz_from_step A c bs i ltac:(lia) ltac:(lia) Hna) in HR; change (bzp bs i) with (bz bs i) in HR;
      pose proof (crc_byte_range c (bz bs i) Hc) as CBR;
      assert (AR : 0 <= A + i < 2 ^ 64) by lia;
      destruct (unpoisoned_check_mu _ lo m m1 A (A + LEN) (A + i) 1 UNP MU WA ALO KLO
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR);
      zstep; zstep; zstep; rewrite sxb_sval; zstep; ck_fast 17 0x809d8 CK;
      pose proof (ck_buf_read m1 A bs i _ BY ltac:(lia) eq_refl) as RDB;
      zstep; cbv beta; rewrite (bz_val bs i BF);
      zstep; zstep; zstep; zstep;
      set (idx := Z.land (Z.lxor (bz bs i) c) 255);
      pose proof (land255_range (Z.lxor (bz bs i) c)) as Hidx; fold idx in Hidx;
      pose proof (ctab_range idx) as CR; pose proof (ctab_addr_range idx Hidx) as TR;
      setreg 13 (Z_to_bv 64 (135264 + 4 * idx))
        ltac:(f_equal; subst idx; rewrite <- crc_idx_form by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; ring);
      destruct (tab_check_mu _ lo m m1 135264 256 idx (ctab_unpoisoned m CKSH) MU WA TL KLO eq_refl Hidx) as (b2 & RD2 & CK2 & SR2);
      pose proof (ctab_read m1 idx (Z_to_bv 64 (135264 + 4 * idx)) MI Hidx eq_refl) as RDT;
      zstep; zstep; zstep; rewrite sxb_sval; zstep; ck_fast 5 0x809fc CK2;
      zstep; rewrite (zx32_lit (ctab idx) CR);
      zstep; zstep; zstep;
      change (Z.lxor (c ≫ 8) (ctab idx)) with (crc_byte c (bz bs i));
      zstep; zstep; (if_cases KE; zify_cond KE; [exfalso; rewrite ?Z.mod_small in KE by lia; lia|]);
      zstep; zstep; zstep; zstep; rewrite land3_mod; if_cases KA; zify_cond KA;
      try (exfalso; clear - KA Hk; lia).
    -
      zstep.
      setreg 11 (Z_to_bv 64 (A + (i + 1))) ltac:(f_equal; lia).
      setreg 7 (Z_to_bv 64 (LEN - (i + 1))) ltac:(f_equal; lia).
      eapply (crcz_blk m1 (i + 1) (crc_byte c (bz bs i)) res); try eassumption; try lia.
      all: first [ (rewrite HR; apply crcz_from_aligned; replace (A + (i + 1)) with (A + i + 1) by lia; exact KA)
                 | (clear - KA Hk Hl Hna; lia) ].
    -
      setreg 10 (Z_to_bv 64 (A + (i + 1))) ltac:(f_equal; lia).
      setreg 12 (Z_to_bv 64 (LEN - (i + 1))) ltac:(f_equal; lia).
      eapply (IH m1 (i + 1) (crc_byte c (bz bs i)) res); try eassumption; try lia.
      all: clear - KA Hk Hl Hna; lia.
  Qed.

  Lemma crcz_main : forall (c : Z) (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    mem_inv asegs m -> stk asegs m lo SP -> rt_got m -> rt_shbase m -> 0 <= c < 2^64 ->
    evtF asegs RNG (POST (crc32_z_model A c bs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 c) (Z_to_bv 64 A) (Z_to_bv 64 LEN) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x80954) fc None m (seg_rom asegs)).
  Proof.
    intros c t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MI ST GOT SHB Hc.
    pose proof BUF as (BY & BF & UNP & RB & RSH).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (zb_length bs) as ZBL.
    pose proof (munch_refl [(SP - 144, SP)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (RL : 0 <= LEN < 2 ^ 64) by lia. assert (RA : 0 <= A < 2 ^ 64) by lia.
    carve_frame 144%nat ST.
    do 14 zstep.
    zstep. if_cases K0; zify_cond K0. { exfalso. rewrite ?Z.mod_small in K0 by lia. lia. }
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (HINV : INV mx) by (split; [eexists; eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption)
    end.
    zstep. zstep. zstep. zstep. zstep. zstep. rewrite crc_pre_form.
    pose proof (crc_pre_range32 c) as CPR.
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    -
      setreg 11 (Z_to_bv 64 (A + 0)) ltac:(f_equal; lia).
      setreg 12 (Z_to_bv 64 (LEN - 0)) ltac:(f_equal; lia).
      eapply (TAIL _ 0 (crc_pre c)); [exact HINV | lia | exact CPR |].
      rewrite crc32_z_model_mid, crc_mid_short by (unfold Zlen; lia). reflexivity.
    - pose proof (crcz_from_0 A c bs ltac:(unfold Zlen; lia)) as E0.
      zstep. rewrite land3_mod. zstep. if_cases KA; zify_cond KA.
      +
        rewrite ?Z.mod_small in KA by lia.
        zstep.
        setreg 11 (Z_to_bv 64 (A + 0)) ltac:(f_equal; lia).
        setreg 7 (Z_to_bv 64 (LEN - 0)) ltac:(f_equal; lia).
        eapply (crcz_blk _ 0 (crc_pre c)); [exact HINV | lia | rewrite Z.add_0_r; exact KA | lia | exact CPR |].
        rewrite E0. apply crcz_from_aligned. rewrite Z.add_0_r. exact KA.
      + rewrite ?Z.mod_small in KA by lia.
        zstep. zstep.
        setreg 10 (Z_to_bv 64 (A + 0)) ltac:(f_equal; lia).
        setreg 12 (Z_to_bv 64 (LEN - 0)) ltac:(f_equal; lia).
        eapply (crcz_align (Z.to_nat (4 - A mod 4 - 1)) _ 0 (crc_pre c)); [exact HINV | lia | | | | exact CPR | exact E0];
          rewrite ?Z.add_0_r; clear - KA K; lia.
  Qed.
End P.
