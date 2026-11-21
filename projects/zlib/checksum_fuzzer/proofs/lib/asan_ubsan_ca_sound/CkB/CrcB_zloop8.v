(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.cks Require Import CkTables CkModel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkA Require Import CrcAGlue CrcAMirror.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit CrcBGlue CrcB_zkit CrcB_ztail.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import StepF.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= crcz_acc_hint.

Lemma crc_fold : forall c b ix, ix = Z.land (Z.lxor b c) 255 -> Z.lxor (c ≫ 8) (ctab ix) = crc_byte c b.
Proof. intros c b ix ->. reflexivity. Qed.

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

  Definition crc8 (c i : Z) : Z :=
    crc_byte (crc_byte (crc_byte (crc_byte (crc_byte (crc_byte (crc_byte (crc_byte c (bz bs i)) (bz bs (i + 1))) (bz bs (i + 2)))
      (bz bs (i + 3))) (bz bs (i + 4))) (bz bs (i + 5))) (bz bs (i + 6))) (bz bs (i + 7)).

  Lemma crc8_skipn : forall c i, 0 <= i -> i + 8 <= LEN ->
    crc_bytes c (skipn (Z.to_nat i) bs) = crc_bytes (crc8 c i) (skipn (Z.to_nat (i + 8)) bs).
  Proof.
    intros c i Hi Hl. unfold crc8.
    rewrite (bz_skipn bs i), crc_bytes_cons by lia.
    rewrite (bz_skipn bs (i + 1)), crc_bytes_cons by lia. replace (i + 1 + 1) with (i + 2) by lia.
    rewrite (bz_skipn bs (i + 2)), crc_bytes_cons by lia. replace (i + 2 + 1) with (i + 3) by lia.
    rewrite (bz_skipn bs (i + 3)), crc_bytes_cons by lia. replace (i + 3 + 1) with (i + 4) by lia.
    rewrite (bz_skipn bs (i + 4)), crc_bytes_cons by lia. replace (i + 4 + 1) with (i + 5) by lia.
    rewrite (bz_skipn bs (i + 5)), crc_bytes_cons by lia. replace (i + 5 + 1) with (i + 6) by lia.
    rewrite (bz_skipn bs (i + 6)), crc_bytes_cons by lia. replace (i + 6 + 1) with (i + 7) by lia.
    rewrite (bz_skipn bs (i + 7)), crc_bytes_cons by lia. replace (i + 7 + 1) with (i + 8) by lia.
    reflexivity.
  Qed.

  Ltac tab_site r MU WA MI :=
    let w := getreg r in
    lazymatch w with
    | Z_to_bv 64 (135136 + Z.lxor ?bexp (Z.land ?cexp 255) ≪ 2) =>
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
        let idx := fresh "idx" in let Hidx := fresh "Hidx" in let CR := fresh "CR" in
        set (idx := Z.land (Z.lxor bexp cexp) 255);
        pose proof (land255_range (Z.lxor bexp cexp)) as Hidx; fold idx in Hidx;
        pose proof (ctab_range idx) as CR;
        setreg r (Z_to_bv 64 (135136 + 4 * idx))
          ltac:(f_equal; subst idx; rewrite <- crc_idx_form by lia; rewrite Z.shiftl_mul_pow2 by lia; change (2^2) with 4; lia);
        let b2 := fresh "b" in let RD2 := fresh "RD" in let CK2 := fresh "CK" in let SR2 := fresh "SR" in let RDT := fresh "RDT" in
        destruct (tab_check_mu _ lo m m1 135136 256 idx (ctab_unpoisoned m CKSH) MU WA
                    ltac:(lia) KLO ltac:(reflexivity) Hidx) as (b2 & RD2 & CK2 & SR2);
        pose proof (ctab_read m1 idx (Z_to_bv 64 (135136 + 4 * idx)) MI Hidx eq_refl) as RDT
      end
    | _ => fail "tab_site: register" r "holds" w
    end.

  Ltac fold_crc :=
    lazymatch goal with
    | |- context [Z.lxor (?c ≫ 8) (ctab ?ix)] =>
        let body := eval unfold ix in ix in
        lazymatch body with
        | Z.land (Z.lxor ?b c) 255 =>
            rewrite (crc_fold c b ix eq_refl);
            let R := fresh "CBR" in assert (R : 0 <= crc_byte c b < 2^32) by (apply crc_byte_range; lia)
        end
    end.

  Ltac byte_site_gen a T OK UNP MU WA PRE :=
    let b := fresh "b" in let RD := fresh "RD" in let CK := fresh "CK" in let SR := fresh "SR" in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (unpoisoned_check_mu _ lo m m1 A (A + LEN) a 1 UNP MU WA
                  ltac:(lia) KLO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RD & CK & SR)
    end;
    PRE; zstep; zstep; zstep; rewrite sxb_sval;
    zstep; rewrite zx32_lit by lia;
    zstep; ck_fast T OK CK; clear RD CK SR.
  Ltac byte_site a T OK UNP MU WA := byte_site_gen a T OK UNP MU WA ltac:(zstep).
  Ltac byte_site0 a T OK UNP MU WA := byte_site_gen a T OK UNP MU WA ltac:(idtac).

  Ltac tab_ck T OK :=
    zstep; zstep; zstep; rewrite sxb_sval; zstep;
    lazymatch goal with CK : sval _ = 0 \/ _ |- _ => ck_fast T OK CK; clear CK end.

  Ltac byte_blk i k ADR :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      lazymatch goal with BY : bytes_at asegs m1 A (zb bs), BF : Forall _ bs |- _ =>
        let RDB := fresh "RDB" in
        pose proof (ck_buf_read m1 A bs (i + k) (Z_to_bv 64 ADR) BY ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDB;
        zstep; cbv beta; rewrite (bz_val bs (i + k) BF)
      end
    end;
    zstep; zstep; fold_crc; zstep; zstep; zstep; zstep.

  Notation L8 pc x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 m1 t3v a1v a2v a6v cv :=
    (MS (mkR x1 (Z_to_bv 64 (SP + -144)) gp tp x5 (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2)) x8 x9
             x10 (Z_to_bv 64 a1v) (Z_to_bv 64 a2v) x13 x14
             (Z_to_bv 64 cv) (Z_to_bv 64 a6v) (Z_to_bv 64 2147450880) (Z_to_bv 64 135136) x19 x20 x21 x22 x23 x24 x25 x26 x27
             (Z_to_bv 64 t3v) (Z_to_bv 64 7) x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs)).

  Definition loop8_post (m1 : amem) (i0 j c : Z)
      (x1 x5 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word) : machine_state -> Prop :=
    fun ms' => exists (x8 x10 x13 x14 x30 x31 : word),
      ms' = L8 0x8162c x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 m1
               (2147450880 + Z.shiftr (A + i0) 3 + (j + 1)) (A + i0) (LEN - (i0 + 8 * (j + 1))) (8 * (j + 1)) (crc8 c (i0 + 8 * j)).

  Lemma crcz_loop8_body : forall (m1 : amem) (i0 j c : Z)
      (x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word),
    INV m1 -> 0 <= i0 -> 0 <= j -> i0 + 8 * j + 8 <= LEN -> 0 <= c < 2^32 ->
    evtF asegs RNG (loop8_post m1 i0 j c x1 x5 x9 x19 x20 x21 x22 x23 x24 x25 x26 x27)
      (L8 0x813d4 x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 m1
          (2147450880 + Z.shiftr (A + i0) 3 + j) (A + i0) (LEN - (i0 + 8 * j)) (8 * j) c).
  Proof.
    intros m1 i0 j c x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 HINV Hi0 Hj Hk Hc.
    pose proof HINV as (FRc & ST & MU & WM & MI & BY).
    pose proof BUF as (BY0 & BF & UNP & RB & RSH).
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia).
    pose proof (ctab_shrng RNG RISH) as RSHT. unfold ACRCTAB in RSHT.
    unfold loop8_post, crc8. set (i := i0 + 8 * j) in *.
    assert (G0 : bv_eqb (Z_to_bv 64 (A + i)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    assert (G1 : bv_eqb (Z_to_bv 64 (A + i + 1)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    assert (G2 : bv_eqb (Z_to_bv 64 (A + i + 2)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    assert (G3 : bv_eqb (Z_to_bv 64 (A + i + 3)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    assert (G4 : bv_eqb (Z_to_bv 64 (A + i + 4)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    assert (G5 : bv_eqb (Z_to_bv 64 (A + i + 5)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    assert (G6 : bv_eqb (Z_to_bv 64 (A + i + 5)) (Z_to_bv 64 (-2)) = false) by (apply guard_beq_m2; lia).
    assert (G7 : bv_eqb (Z_to_bv 64 (A + i + 7)) (Z_to_bv 64 (-1)) = false) by (apply guard_beq_m1; lia).
    pose proof (bz_range bs i BF) as BR0. pose proof (bz_range bs (i + 1) BF) as BR1.
    pose proof (bz_range bs (i + 2) BF) as BR2. pose proof (bz_range bs (i + 3) BF) as BR3.
    pose proof (bz_range bs (i + 4) BF) as BR4. pose proof (bz_range bs (i + 5) BF) as BR5.
    pose proof (bz_range bs (i + 6) BF) as BR6. pose proof (bz_range bs (i + 7) BF) as BR7.
    zstep.
    setreg 10 (Z_to_bv 64 (A + i)) ltac:(f_equal; subst i; lia).
    zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G0).
    zstep. zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G1).
    zstep. zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G2).
    zstep. zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G3).
    zstep. zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G4).
    zstep. zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G5).
    zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G6).
    zstep. zstep. apply (evtF_if_false _ _ _ _ _ _ _ _ _ _ _ G7).
    clear G0 G1 G2 G3 G4 G5 G6 G7.
    destruct (unpoisoned_check_mu _ lo m m1 A (A + LEN) (A + i) 1 UNP MU WA
                ltac:(lia) KLO ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b0 & RD0 & CK0 & SR0).
    replace (Z.shiftr (A + i) 3 + 2147450880) with (2147450880 + Z.shiftr (A + i0) 3 + j) in RD0
      by (subst i; replace (A + (i0 + 8 * j)) with (A + i0 + 8 * j) by lia; rewrite shiftr3_off by lia; lia).
    zstep. rewrite sxb_sval. zstep.
    ck_fast 31 0x81418 CK0. clear RD0 CK0 SR0.
    pose proof (ck_buf_read m1 A bs i (Z_to_bv 64 (A + i + 7 + -7)) BY ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDB0.
    zstep. cbv beta. rewrite (bz_val bs i BF).
    zstep. zstep. zstep. zstep.
    tab_site 14 MU WA MI.
    tab_ck 8 0x8143c.
    byte_site0 (A + i + 1) 8 0x81450 UNP MU WA.
    byte_blk i 1 (A + i + 7 + -6). tab_site 13 MU WA MI. tab_ck 31 0x8147c. byte_site (A + i + 2) 8 0x81494 UNP MU WA.
    byte_blk i 2 (A + i + 7 + -5). tab_site 13 MU WA MI. tab_ck 31 0x814c0. byte_site (A + i + 3) 8 0x814d8 UNP MU WA.
    byte_blk i 3 (A + i + 7 + -4). tab_site 13 MU WA MI. tab_ck 31 0x81504. byte_site (A + i + 4) 8 0x8151c UNP MU WA.
    byte_blk i 4 (A + i + 7 + -3). tab_site 13 MU WA MI. tab_ck 31 0x81548. byte_site (A + i + 5) 8 0x81560 UNP MU WA.
    byte_blk i 5 (A + i + 7 + -2). tab_site 13 MU WA MI. tab_ck 31 0x8158c. byte_site (A + i + 6) 8 0x815a4 UNP MU WA.
    byte_blk i 6 (A + i + 7 + -1). tab_site 13 MU WA MI. tab_ck 31 0x815d0. byte_site (A + i + 7) 31 0x815e8 UNP MU WA.
    byte_blk i 7 (A + i + 7). tab_site 10 MU WA MI. tab_ck 15 0x81614.
    zstep. rewrite zx32_lit by lia.
    zstep. zstep. zstep. zstep. fold_crc. zstep.
    setreg 28 (Z_to_bv 64 (2147450880 + Z.shiftr (A + i0) 3 + (j + 1))) ltac:(f_equal; lia).
    setreg 12 (Z_to_bv 64 (LEN - (i0 + 8 * (j + 1)))) ltac:(f_equal; subst i; lia).
    setreg 16 (Z_to_bv 64 (8 * (j + 1))) ltac:(f_equal; lia).
    apply evtF_done. do 6 eexists. reflexivity.
  Qed.

  Lemma crcz_loop8 : forall (k : nat) (m1 : amem) (i0 j c res : Z)
      (x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word),
    INV m1 -> 0 <= i0 -> 0 <= j -> 8 * Z.of_nat (S k) <= LEN - (i0 + 8 * j) < 8 * Z.of_nat (S k) + 8 -> 0 <= c < 2^32 ->
    res = Z.lxor (crc_bytes c (skipn (Z.to_nat (i0 + 8 * j)) bs)) M32 ->
    evtF asegs RNG (POST res)
      (L8 0x813d4 x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 m1
          (2147450880 + Z.shiftr (A + i0) 3 + j) (A + i0) (LEN - (i0 + 8 * j)) (8 * j) c).
  Proof.
    induction k as [|k IH];
      intros m1 i0 j c res x1 x5 x8 x9 x10 x13 x14 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 HINV Hi0 Hj Hk Hc HR;
      pose proof KLO as KLO'; unfold KHIGH in KLO'; pose_sp_range sp;
      pose proof HINV as (FRc & ST & MU & WM & MI & BY);
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
      rewrite (crc8_skipn c (i0 + 8 * j)) in HR by lia;
      assert (C8R : 0 <= crc8 c (i0 + 8 * j) < 2^32) by (unfold crc8; repeat apply crc_byte_range; exact Hc);
      (eapply evtF_cut; [eapply (crcz_loop8_body m1 i0 j c); first [exact HINV | lia]|]);
      cbv beta; intros ms' (y8 & y10 & y13 & y14 & y30 & y31 & ->);
      zstep; if_cases K; zify_cond K.
    - exfalso. lia.
    -
      zstep. zstep.
      setreg 11 (Z_to_bv 64 (A + (i0 + 8 * (j + 1)))) ltac:(f_equal; lia).
      eapply crcz_bytes with (i := i0 + 8 * (j + 1)) (c := crc8 c (i0 + 8 * j)); try eassumption; try lia.
      rewrite HR. replace (i0 + 8 * j + 8) with (i0 + 8 * (j + 1)) by lia. reflexivity.
    - eapply (IH m1 i0 (j + 1) (crc8 c (i0 + 8 * j))); [exact HINV| lia | lia | lia | exact C8R|].
      rewrite HR. replace (i0 + 8 * j + 8) with (i0 + 8 * (j + 1)) by lia. reflexivity.
    - exfalso. lia.
  Qed.

  Lemma crcz_tail : crcz_tail_stmt RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo A bs.
  Proof.
    unfold crcz_tail_stmt.
    intros m1 i c res x1 x5 x6 x7 x8 x9 x10 x13 x14 x16 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HINV Hi Hc HR.
    pose proof KLO as KLO'. unfold KHIGH in KLO'. pose_sp_range sp.
    pose proof HINV as (FRc & ST & MU & WM & MI & BY).
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    zstep. zstep. if_cases K; zify_cond K.
    - eapply crcz_bytes with (i := i) (c := c); try eassumption.
    - zstep. zstep. zstep. zstep. zstep. zstep.
      setreg 28 (Z_to_bv 64 (2147450880 + Z.shiftr (A + i) 3 + 0)) ltac:(f_equal; lia).
      setreg 12 (Z_to_bv 64 (LEN - (i + 8 * 0))) ltac:(f_equal; lia).
      setreg 16 (Z_to_bv 64 (8 * 0)) ltac:(reflexivity).
      eapply (crcz_loop8 (Z.to_nat ((LEN - i) / 8 - 1)) m1 i 0 c); try eassumption; try lia.
      rewrite HR. replace (i + 8 * 0) with i by lia. reflexivity.
  Qed.
End P.
