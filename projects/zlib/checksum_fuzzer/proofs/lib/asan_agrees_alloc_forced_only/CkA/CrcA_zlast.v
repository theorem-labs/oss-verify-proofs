(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit CrcAGlue CrcAMirror CrcA_zkit.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
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

  Notation SP := (bv_unsigned sp).
  Notation LEN := (Z.of_nat (length bs)).
  Notation INV m1 := (crcz_inv ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SP lo A bs m m1).
  Notation POST res := (ck_postA 144 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc res lo m).

  Ltac ctabY_site MU WA MI TL :=
    let w := getreg 10 in
    lazymatch w with
    | Z_to_bv 64 (135264 + Z.land ?y 255 ≪ 2) =>
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
        setreg 10 (Z_to_bv 64 (135264 + 4 * Z.land y 255)) ltac:(f_equal; apply ctab_addr_form);
        let idx := fresh "idx" in let Hidx := fresh "Hidx" in let SX := fresh "SX" in let CR := fresh "CR" in
        set (idx := Z.land y 255);
        pose proof (land255_range y) as Hidx; fold idx in Hidx;
        pose proof (sxz_range (ctab idx)) as SX; pose proof (ctab_range64 idx) as CR;
        let TR := fresh "TR" in pose proof (ctab_addr_range idx Hidx) as TR;
        let b2 := fresh "b" in let RD2 := fresh "RD" in let CK2 := fresh "CK" in let SR2 := fresh "SR" in let RDT := fresh "RDT" in
        destruct (tab_check_mu _ lo m m1 135264 256 idx (ctab_unpoisoned m CKSH) MU WA TL KLO eq_refl Hidx) as (b2 & RD2 & CK2 & SR2);
        pose proof (ctab_read m1 idx (Z_to_bv 64 (135264 + 4 * idx)) MI Hidx eq_refl) as RDT
      end
    | _ => fail "ctabY_site: a0 holds" w
    end.

  Ltac tabY_ck U OK :=
    zstep; zstep; zstep; rewrite sxb_sval; zstep;
    lazymatch goal with CK : sval _ = 0 \/ _ |- _ => ck_fast U OK CK; clear CK end.

  Ltac word_ck a U OK UNP MU WA WK :=
    let b := fresh "b" in let RD := fresh "RD" in let CK := fresh "CK" in let SR := fresh "SR" in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?m1 _) =>
      destruct (unpoisoned_check_mu _ lo m m1 A (A + LEN) a 4 UNP MU WA ALO KLO
                  (proj1 WK) (proj1 (proj2 WK)) (proj1 (proj2 (proj2 WK))) (proj2 (proj2 (proj2 WK)))) as (b & RD & CK & SR)
    end;
    zstep; zstep; zstep; zstep; rewrite sxb_sval;
    zstep;
    lazymatch goal with |- context [sx32 (Z_to_bv 64 (ctab ?ix))] => rewrite (sx32_sxz (ctab ix) (ctab_range64 ix)) end;
    zstep; ck_fast U OK CK; clear RD CK SR.

  Ltac absorb1 Y' :=
    lazymatch goal with
    | |- context [Z.lxor ((?y mod 4294967296) ≫ 8) (sxz (ctab ?ix))] =>
        subst ix; rewrite <- (dY1_unfold y);
        let R := fresh "R" Y' in let M := fresh "M" Y' in
        pose proof (dY1_range y) as R; pose proof (dY1_mod32 y) as M;
        let E := fresh "E" in remember (dY1 y) as Y' eqn:E; clear E
    end.

  Ltac round1 U OK Y' MU WA MI TL :=
    zstep; zstep; zstep; ctabY_site MU WA MI TL; tabY_ck U OK;
    zstep;
    lazymatch goal with |- context [sx32 (Z_to_bv 64 (ctab ?ix))] => rewrite (sx32_sxz (ctab ix) (ctab_range64 ix)) end;
    zstep; rewrite srliw8_form;
    zstep; absorb1 Y'.

  Ltac absorbN Y' :=
    lazymatch goal with
    | |- context [Z.lxor (Z.lxor (sxz (ctab ?ix)) ?x) (Z.lxor (sxz ?w) ((?y mod 4294967296) ≫ 8))] =>
        subst ix; rewrite <- (dYn_unfold y x w);
        let R := fresh "R" Y' in let M := fresh "M" Y' in
        pose proof (dYn_range y x w ltac:(assumption)) as R; pose proof (dYn_mod32 y x w ltac:(assumption)) as M;
        let E := fresh "E" in remember (dYn y x w) as Y' eqn:E; clear E
    end.

  Ltac roundN U1 OK1 a w U2 OK2 Y' UNP MU WA MI TL WK RW :=
    zstep; zstep; zstep; ctabY_site MU WA MI TL; tabY_ck U1 OK1;
    word_ck a U2 OK2 UNP MU WA WK;
    zstep; rewrite (sx32_sxz w RW);
    zstep; rewrite srliw8_form;
    zstep; zstep; zstep; absorbN Y'.

  Section D.
    Variables (m1 : amem) (iL x0 x1 x2 x3 x4 n1 blks : Z)
              (x1r x9 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 : word).
    Hypothesis HINV : INV m1.
    Hypothesis Hi : 0 <= iL.
    Hypothesis Hl : iL + 20 <= LEN.
    Hypothesis Hal : (A + iL) mod 4 = 0.
    Hypothesis R0 : 0 <= x0 < 2^64.
    Hypothesis R1 : 0 <= x1 < 2^64.
    Hypothesis R2 : 0 <= x2 < 2^64.
    Hypothesis R3 : 0 <= x3 < 2^64.
    Hypothesis R4 : 0 <= x4 < 2^64.
    Hypothesis Rn : 0 <= n1 < 2^64.
    Hypothesis Rb : 0 <= blks < 2^64.

    Notation DST pc x5 x6 x10 x12 x13 x14 x17 :=
      (MS (mkR x1r (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 n1) (Z_to_bv 64 x2) x9 x10 (Z_to_bv 64 (A + iL)) x12 x13 x14
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 blks) x29 (Z_to_bv 64 x3) (Z_to_bv 64 x0))
          F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs)).

    Definition dword_post (pc : Z) (x14 : word) (E : Z) : machine_state -> Prop :=
      fun ms' => exists (Y' : Z) (x5 x6 x10 x13 x17 : word),
        ms' = DST pc x5 x6 x10 (Z_to_bv 64 Y') x13 x14 x17 /\ 0 <= Y' < 2^64 /\ Y' mod 2^32 = E.

    Lemma d_wk : forall off, off = 4 \/ off = 8 \/ off = 12 \/ off = 16 ->
      A <= A + iL + off /\ A + iL + off + 4 <= A + LEN /\ 1 <= 4 /\ (A + iL + off) mod 8 + 4 <= 8.
    Proof. intros off H. repeat split; try lia; Z.div_mod_to_equations; lia. Qed.

    Lemma d_rw : forall off, 0 <= off <= 16 ->
      ov_read_bytes asegs m1 (Z_to_bv 64 (A + iL + off)) 4 = Some (le4 (Z_to_bv 64 (wdp bs (iL + off)))).
    Proof.
      intros off H. destruct HINV as (_ & _ & _ & _ & _ & BY). destruct BUF as (_ & BF & _).
      apply (ck_buf_read4 m1 A bs (iL + off) _ BY BF); [lia | lia | unfold wa; f_equal; lia].
    Qed.

    Lemma d_ar : forall off, 0 <= off <= 20 -> 0 <= A + iL + off < 2 ^ 64.
    Proof. intros off H. destruct HINV as (_ & ST & _). destruct ST as (L0 & _). pose proof KLO as K. unfold KHIGH in K. pose_sp_range sp. lia. Qed.

    Lemma d_tl : 135264 + 4 * 256 <= lo.
    Proof. pose proof KLO as K. unfold KHIGH in K. lia. Qed.

    Ltac d_setup :=
      pose proof HINV as (FRc & ST & MU & WM & MI & BY);
      pose proof BUF as (BY0 & BF & UNP & RB & RSH);
      pose proof KLO as KLO'; unfold KHIGH in KLO'; pose_sp_range sp;
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption);
      assert (WA : wabove [(SP - 144, SP)] lo) by (cbn; lia);
      pose proof (ctab_shrng RNG RISH) as RSHT; unfold ACRCTAB in RSHT;
      pose proof d_tl as TL; pose_zr_lits.

    Ltac d_close Y' :=
      apply evtF_done; unfold dword_post; exists Y'; do 5 eexists;
      split; [reflexivity|]; split; [assumption|].

    Lemma dword0 : forall (x5 x6 x10 x12 x17 : word),
      evtF asegs RNG (dword_post 0x8111c (Z_to_bv 64 x4)
                        (Z.lxor (Z.lxor (x1 mod 2^32) (wdp bs (iL + 4))) (crc_word (Z.lxor (x0 mod 2^32) (wdp bs iL)))))
           (DST 0x81054 x5 x6 x10 x12 (Z_to_bv 64 x1) (Z_to_bv 64 x4) x17).
    Proof.
      intros x5 x6 x10 x12 x17. d_setup.
      set (w0 := wdp bs iL). set (w1 := wdp bs (iL + 4)).
      pose proof (wdp_range bs iL BF) as W0R. fold w0 in W0R. pose proof (sxz_range w0) as SW0.
      pose proof (wdp_range bs (iL + 4) BF) as W1R. fold w1 in W1R. pose proof (sxz_range w1) as SW1.
      pose proof (wdp_range64 bs iL BF) as W0R64. fold w0 in W0R64.
      pose proof (wdp_range64 bs (iL + 4) BF) as W1R64. fold w1 in W1R64.
      pose proof (d_rw 0 ltac:(lia)) as RW0. rewrite !Z.add_0_r in RW0. fold w0 in RW0.
      pose proof (d_rw 4 ltac:(lia)) as RW1. fold w1 in RW1.
      pose proof (d_wk 4 ltac:(lia)) as WK. pose proof (d_ar 4 ltac:(lia)) as AR.
      zstep. rewrite (sx32_sxz w0 W0R64).
      zstep.
      rewrite <- (dY0_unfold w0 x0).
      pose proof (dY0_range w0 x0 R0) as RY00. pose proof (dY0_mod32 w0 x0 W0R) as MY00.
      remember (dY0 w0 x0) as Y00 eqn:EY; clear EY.
      round1 5 0x81078 Y01 MU WA MI TL.
      round1 5 0x810a0 Y02 MU WA MI TL.
      round1 5 0x810c8 Y03 MU WA MI TL.
      roundN 5 0x810f0 (A + iL + 4) w1 6 0x81108 Y10 UNP MU WA MI TL WK W1R64.
      d_close Y10.
      rewrite MY10, MY03, MY02, MY01, MY00. reflexivity.
    Qed.

    Ltac dword_tac off OK1 OK2 OK3 OK4 OK5 BF UNP MU WA MI TL :=
      let w := fresh "w" in let WR := fresh "WR" in let SW := fresh "SW" in let WR64 := fresh "WR64" in
      let RW := fresh "RW" in let WK := fresh "WK" in
      let Ya := fresh "Ya" in let Yb := fresh "Yb" in let Yc := fresh "Yc" in let Yd := fresh "Yd" in
      set (w := wdp bs (iL + off));
      pose proof (wdp_range bs (iL + off) BF) as WR; fold w in WR; pose proof (sxz_range w) as SW;
      pose proof (wdp_range64 bs (iL + off) BF) as WR64; fold w in WR64;
      pose proof (d_rw off ltac:(lia)) as RW; fold w in RW;
      pose proof (d_wk off ltac:(lia)) as WK; let AR := fresh "AR" in pose proof (d_ar off ltac:(lia)) as AR;
      round1 17 OK1 Ya MU WA MI TL;
      round1 17 OK2 Yb MU WA MI TL;
      round1 17 OK3 Yc MU WA MI TL;
      roundN 17 OK4 (A + iL + off) w 5 OK5 Yd UNP MU WA MI TL WK WR64;
      d_close Yd;
      repeat match goal with M : ?y mod 2^32 = _ |- context [?y mod 2^32] => rewrite M end;
      reflexivity.

    Lemma dword1 : forall (Y : Z) (x5 x6 x10 x13 x17 : word), 0 <= Y < 2^64 ->
      evtF asegs RNG (dword_post 0x811dc (Z_to_bv 64 x4)
                        (Z.lxor (Z.lxor (x2 mod 2^32) (wdp bs (iL + 8))) (crc_word (Y mod 2^32))))
           (DST 0x8111c x5 x6 x10 (Z_to_bv 64 Y) x13 (Z_to_bv 64 x4) x17).
    Proof.
      intros Y x5 x6 x10 x13 x17 RY. d_setup.
      dword_tac 8 0x81138 0x81160 0x81188 0x811b0 0x811c8 BF UNP MU WA MI TL.
    Qed.

    Lemma dword2 : forall (Y : Z) (x5 x6 x10 x13 x17 : word), 0 <= Y < 2^64 ->
      evtF asegs RNG (dword_post 0x8129c (Z_to_bv 64 x4)
                        (Z.lxor (Z.lxor (x3 mod 2^32) (wdp bs (iL + 12))) (crc_word (Y mod 2^32))))
           (DST 0x811dc x5 x6 x10 (Z_to_bv 64 Y) x13 (Z_to_bv 64 x4) x17).
    Proof.
      intros Y x5 x6 x10 x13 x17 RY. d_setup.
      dword_tac 12 0x811f8 0x81220 0x81248 0x81270 0x81288 BF UNP MU WA MI TL.
    Qed.

    Lemma dword3 : forall (Y : Z) (x5 x6 x10 x13 x17 : word), 0 <= Y < 2^64 ->
      evtF asegs RNG (dword_post 0x8135c (Z_to_bv 64 x4)
                        (Z.lxor (Z.lxor (x4 mod 2^32) (wdp bs (iL + 16))) (crc_word (Y mod 2^32))))
           (DST 0x8129c x5 x6 x10 (Z_to_bv 64 Y) x13 (Z_to_bv 64 x4) x17).
    Proof.
      intros Y x5 x6 x10 x13 x17 RY. d_setup.
      dword_tac 16 0x812b8 0x812e0 0x81308 0x81330 0x81348 BF UNP MU WA MI TL.
    Qed.

    Lemma dword4 : forall (Y res : Z) (x5 x6 x10 x13 x14 x17 : word), 0 <= Y < 2^64 ->
      n1 - 20 * blks = LEN - (iL + 20) ->
      res = Z.lxor (crc_bytes (crc_word (Y mod 2^32)) (skipn (Z.to_nat (iL + 20)) bs)) M32 ->
      evtF asegs RNG (POST res) (DST 0x8135c x5 x6 x10 (Z_to_bv 64 Y) x13 x14 x17).
    Proof.
      intros Y res x5 x6 x10 x13 x14 x17 RY Hn HR. d_setup.
      round1 14 0x81378 Y1 MU WA MI TL.
      round1 14 0x813a0 Y2 MU WA MI TL.
      round1 14 0x813c8 Y3 MU WA MI TL.
      zstep; zstep; zstep. ctabY_site MU WA MI TL. tabY_ck 14 0x813f0.
      zstep. zstep.
      lazymatch goal with |- context [zx32 (Z_to_bv 64 (ctab ?ix))] => rewrite (zx32_lit (ctab ix) (ctab_range ix)) end.
      zstep. rewrite srliw8_form.
      zstep. zstep. zstep. zstep.
      setreg 12 (Z_to_bv 64 (LEN - (iL + 20))) ltac:(apply (d_len n1 blks _ Hn)).
      setreg 11 (Z_to_bv 64 (A + (iL + 20))) ltac:(f_equal; apply Z.add_assoc).
      lazymatch goal with |- context [Z.lxor ((?y mod 4294967296) ≫ 8) (ctab ?ix)] =>
        subst ix; rewrite <- (dYf_unfold y) end.
      eapply (TAIL m1 (iL + 20) (dYf Y3) res); [exact HINV| lia | | ].
      - rewrite dYf_eq. apply crc_word1_range32. apply Z.mod_pos_bound. lia.
      - rewrite HR, dYf_eq. unfold crc_word. rewrite MY3, MY2, MY1. reflexivity.
    Qed.

    Lemma crcz_last_body : forall (res : Z) (x5 x6 x10 x12 x17 : word),
      n1 - 20 * blks = LEN - (iL + 20) ->
      res = Z.lxor (crc_bytes (braid_last [x0 mod 2^32; x1 mod 2^32; x2 mod 2^32; x3 mod 2^32; x4 mod 2^32]
                                          (firstn 20 (skipn (Z.to_nat iL) bs)))
                              (skipn (Z.to_nat (iL + 20)) bs)) M32 ->
      evtF asegs RNG (POST res) (DST 0x81054 x5 x6 x10 x12 (Z_to_bv 64 x1) (Z_to_bv 64 x4) x17).
    Proof.
      intros res x5 x6 x10 x12 x17 Hn HR.
      rewrite (braid_last_5 _ _ _ _ _ _ _ _ _ _ _ (block20_words bs iL Hi Hl)) in HR.
      eapply evtF_cut; [apply dword0|]. cbv beta. intros ms' (Y1 & y5 & y6 & y10 & y13 & y17 & -> & RY1 & MY1).
      eapply evtF_cut; [apply (dword1 Y1); exact RY1|]. cbv beta. intros ms' (Y2 & z5 & z6 & z10 & z13 & z17 & -> & RY2 & MY2).
      eapply evtF_cut; [apply (dword2 Y2); exact RY2|]. cbv beta. intros ms' (Y3 & u5 & u6 & u10 & u13 & u17 & -> & RY3 & MY3).
      eapply evtF_cut; [apply (dword3 Y3); exact RY3|]. cbv beta. intros ms' (Y4 & v5 & v6 & v10 & v13 & v17 & -> & RY4 & MY4).
      apply (dword4 Y4 res); [exact RY4| exact Hn|].
      rewrite HR, MY4, MY3, MY2, MY1. reflexivity.
    Qed.
  End D.

  Lemma crcz_last : forall (m1 : amem) (iL x0 x1 x2 x3 x4 n1 blks res : Z)
      (x1r x5 x6 x9 x10 x12 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 : word),
    INV m1 -> 0 <= iL -> iL + 20 <= LEN -> (A + iL) mod 4 = 0 ->
    0 <= x0 < 2^64 -> 0 <= x1 < 2^64 -> 0 <= x2 < 2^64 -> 0 <= x3 < 2^64 -> 0 <= x4 < 2^64 ->
    0 <= n1 < 2^64 -> 0 <= blks < 2^64 -> n1 - 20 * blks = LEN - (iL + 20) ->
    res = Z.lxor (crc_bytes (braid_last [x0 mod 2^32; x1 mod 2^32; x2 mod 2^32; x3 mod 2^32; x4 mod 2^32]
                                        (firstn 20 (skipn (Z.to_nat iL) bs)))
                            (skipn (Z.to_nat (iL + 20)) bs)) M32 ->
    evtF asegs RNG (POST res)
      (MS (mkR x1r (Z_to_bv 64 (SP + -144)) gp tp x5 x6 (Z_to_bv 64 n1) (Z_to_bv 64 x2) x9 x10 (Z_to_bv 64 (A + iL)) x12 (Z_to_bv 64 x1) (Z_to_bv 64 x4)
               (Z_to_bv 64 2147450880) (Z_to_bv 64 135264) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 blks) x29 (Z_to_bv 64 x3) (Z_to_bv 64 x0))
          F (Z_to_bv 64 0x81054) fc None m1 (seg_rom asegs)).
  Proof.
    intros m1 iL x0 x1 x2 x3 x4 n1 blks res x1r x5 x6 x9 x10 x12 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29
           HINV Hi Hl Hal R0 R1 R2 R3 R4 Rn Rb Hn HR.
    apply crcz_last_body; assumption.
  Qed.
End P.
