(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW3.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_blk_iface RZ_bfse_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Section C.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z).
  Hypothesis HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm.
  Notation POST t := (bf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W tl wlen lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation BFm := (BF ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W tl k wlen norm).

  (* [comment removed for export] *)
  Notation STP pc mm xra x6e x7e xs0 xs1 xa0 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 (2^tl + -1)) x6e x7e xs0 xs1 xa0 (Z_to_bv 64 NC) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 BASE) (Z_to_bv 64 BITS)
        (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 8)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31).
  Notation ST1 pc mm xra xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 :=
    (STP pc mm xra (Z_to_bv 64 (W + 106)) (Z_to_bv 64 (maxSV + 1)) (Z_to_bv 64 (W + 2 * (maxSV + 1))) (Z_to_bv 64 65535) xa0
         xs2 xs3 xs4 xs5 (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 x28 x29 x30 (Z_to_bv 64 (2^(tl + -1)))).


  (* [comment removed for export] *)
  Notation STC pc mm xra xs xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xhigh xpos xstep xn :=
    (STP pc mm xra xs (Z_to_bv 64 (maxSV + 1)) xi xs1 xa0 xs2 xs3 xs4 xs5 (Z_to_bv 64 DT) xs7 xs8 xs9 xs10 xs11 xhigh xpos xstep xn).

  (* [comment removed for export] *)
  Lemma bf_skip : forall (t : seq_table) (fu : nat) m1 high step p xra xs xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xn,
    0 <= high < 2^tl -> 0 <= p < 2^tl -> 0 <= step < 1048576 ->
    skip_low fu (2^tl) step high ((p + step) mod 2^tl) <= high ->
    (forall ya0, evt psegs (POST t)
       (STC 0x16a20 m1 xra xs xi xs1 ya0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
            (Z_to_bv 64 (skip_low fu (2^tl) step high ((p + step) mod 2^tl))) (Z_to_bv 64 step) xn)) ->
    evt psegs (POST t)
       (STC 0x16a14 m1 xra xs xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high) (Z_to_bv 64 p) (Z_to_bv 64 step) xn).
  Proof.
    intros t fu. induction fu as [|fu IH]; intros until xn; intros HH HP HST SK KONT.
    all: destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    all: assert (QR : 0 <= (p + step) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; rewrite (swrap32_small (step + p)) by lia; zstep;
         replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); rewrite (Z.land_ones (step + p) tl) by lia;
         replace (step + p) with (p + step) by lia;
         replace (Z.ones tl) with (2^tl + -1) by (rewrite Z.ones_equiv; lia).
    all: zstep; if_cases K; zify_cond K.
    - exfalso. cbn [skip_low] in SK. lia.
    - cbn [skip_low] in SK, KONT. apply KONT.
    - cbn [skip_low] in SK, KONT. destruct (Z.ltb_spec high ((p + step) mod 2^tl)); [|lia].
      eapply (IH m1 high step ((p + step) mod 2^tl)); [exact HH | exact QR | exact HST | exact SK | exact KONT].
    - cbn [skip_low] in SK, KONT. destruct (Z.ltb_spec high ((p + step) mod 2^tl)); [lia|]. apply KONT.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_place_n : forall (t : seq_table) (kk : nat) m1 h0 h1 w8 w16 cells symNext spread s i n position high
                            xra xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= s <= 52 -> 0 <= i -> i + Z.of_nat (S kk) = n -> n <= 2^tl -> 0 <= position < 2^tl -> 0 <= high < 2^tl ->
    (forall m2 cells' position' ya0,
       place_n (S kk) (2^tl) (fse_tablestep (2^tl)) high s position cells = (cells', position') ->
       BFm h0 h1 w8 w16 cells' symNext spread m2 -> 0 <= position' < 2^tl ->
       evt psegs (POST t)
         (STC 0x16a28 m2 xra (Z_to_bv 64 s) (Z_to_bv 64 n) xs1 ya0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
              (Z_to_bv 64 position') (Z_to_bv 64 (fse_tablestep (2^tl))) (Z_to_bv 64 n))) ->
    evt psegs (POST t)
      (STC 0x16a04 m1 xra (Z_to_bv 64 s) (Z_to_bv 64 i) xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
           (Z_to_bv 64 position) (Z_to_bv 64 (fse_tablestep (2^tl))) (Z_to_bv 64 n)).
  Proof.
    intros t kk. induction kk as [|kk IH]; intros until xs11; intros I HS HI HIN HN HP HH KONT; open_bh HY; open_bf I.
    all: destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    all: assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    all: assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    all: unfold FseNCount.Zlength in *.
    all: assert (STEPR : 0 <= fse_tablestep (2^tl) < 1048576) by (unfold fse_tablestep; Z.div_mod_to_equations; lia).
    all: zstep; zstep; rewrite (zext32_sh29 position) by lia; zstep.
    all: cst CEL position 4 4%nat cellsB_store_base (2^32).
    all: rewrite (Z.mod_small s (2^32)) in CEL by lia.
    all: rewrite <- (set_base_as_set_cell cells position s) in CEL by (unfold FseNCount.Zlength; lia).
    all: assert (CLEN' : zlenF (set_base position s cells) = 2^tl) by (unfold FseNCount.Zlength; rewrite set_base_length; exact CLEN).
    all: assert (QR : 0 <= (position + fse_tablestep (2^tl)) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: pose proof (skip_low_term tl high ((position + fse_tablestep (2^tl)) mod 2^tl) TL9 ltac:(lia) QR) as SKT.
    all: eapply (bf_skip t (Z.to_nat (2^tl)) m0 high (fse_tablestep (2^tl)) position); [exact HH | exact HP | exact STEPR | exact SKT |].
    all: intros ya0; fold (next_pos (2^tl) (fse_tablestep (2^tl)) high position).
    all: assert (NPR : 0 <= next_pos (2^tl) (fse_tablestep (2^tl)) high position < 2^tl).
    all: try (unfold next_pos; split; [|lia];
              assert (SLN : forall f q, 0 <= q -> 0 <= skip_low f (2^tl) (fse_tablestep (2^tl)) high q)
                by (induction f as [|f IHf]; intros q Hq; cbn [skip_low]; [exact Hq| destruct (high <? q); [apply IHf; apply Z.mod_pos_bound; lia | exact Hq]]);
              apply SLN; lia).
    all: zstep; rewrite (swrap32_small (i + 1)) by lia; zstep; if_cases K; zify_cond K.
    - exfalso; lia.
    - replace (i + 1) with n by lia.
      eapply KONT; [cbn [place_n]; reflexivity | close_bf | exact NPR].
    - eapply (IH m0 h0 h1 w8 w16 (set_base position s cells) symNext spread s (i + 1) n (next_pos (2^tl) (fse_tablestep (2^tl)) high position) high);
        [close_bf | exact HS | lia | lia | exact HN | exact NPR | exact HH |].
      intros m2 cells' position' ya1 PN I2 HP2. eapply KONT; [| exact I2 | exact HP2].
      cbn [place_n]. exact PN.
    - exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow_next : forall (t : seq_table) m1 s xra xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xhigh xpos xstep xn,
    0 <= s <= maxSV ->
    (s + 1 < maxSV + 1 -> evt psegs (POST t) (STC 0x169f0 m1 xra (Z_to_bv 64 (s + 1)) xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xhigh xpos xstep xn)) ->
    (s + 1 = maxSV + 1 -> evt psegs (POST t) (STC 0x16a9c m1 xra (Z_to_bv 64 (maxSV + 1)) xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xhigh xpos xstep xn)) ->
    evt psegs (POST t) (STC 0x169e8 m1 xra (Z_to_bv 64 s) xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xhigh xpos xstep xn).
  Proof.
    intros until xn; intros HS KH KE.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    zstep. zstep. if_cases K; zify_cond K.
    - replace (s + 1) with (maxSV + 1) by lia. apply KE. lia.
    - apply KH. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow_body : forall (t : seq_table) m1 h0 h1 w8 w16 cells symNext spread s position high
                              xra xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xn,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= s <= maxSV -> 0 <= position < 2^tl -> high + 1 = nsum norm (maxSV + 1) ->
    (forall m2 cells' p' yi ya0 yn,
       place_n (Z.to_nat (Znth s norm)) (2^tl) (fse_tablestep (2^tl)) high s position cells = (cells', p') -> s + 1 < maxSV + 1 ->
       BFm h0 h1 w8 w16 cells' symNext spread m2 -> 0 <= p' < 2^tl ->
       evt psegs (POST t) (STC 0x169f0 m2 xra (Z_to_bv 64 (s + 1)) yi xs1 ya0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
                               (Z_to_bv 64 p') (Z_to_bv 64 (fse_tablestep (2^tl))) yn)) ->
    (forall m2 cells' p' yi ya0 yn,
       place_n (Z.to_nat (Znth s norm)) (2^tl) (fse_tablestep (2^tl)) high s position cells = (cells', p') -> s + 1 = maxSV + 1 ->
       BFm h0 h1 w8 w16 cells' symNext spread m2 -> 0 <= p' < 2^tl ->
       evt psegs (POST t) (STC 0x16a9c m2 xra (Z_to_bv 64 (maxSV + 1)) yi xs1 ya0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
                               (Z_to_bv 64 p') (Z_to_bv 64 (fse_tablestep (2^tl))) yn)) ->
    evt psegs (POST t) (STC 0x169f0 m1 xra (Z_to_bv 64 s) xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
                            (Z_to_bv 64 position) (Z_to_bv 64 (fse_tablestep (2^tl))) xn).
  Proof.
    intros until xn; intros I HS HP HHN KH KE; open_bh HY.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    assert (NR : -1 <= Znth s norm <= 2^tl).
    { pose proof (NGE s ltac:(lia)). pose proof (count_le_size norm maxSV tl TL9 NLEN NGE NSUM s ltac:(lia)) as CL. unfold weight in CL.
      destruct (Z.eqb_spec (Znth s norm) (-1)); lia. }
    pose proof I as I'. open_bf I'. unfold FseNCount.Zlength in *.
    zstep. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth psegs m1 NC norm s a NCB ltac:(lia) ltac:(unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia)) as RD end.
    zstep. rewrite (sx16_short (Znth s norm)) by lia.
    zstep. if_cases K; zify_cond K.
    - assert (NLE : Znth s norm <= 0).
      { destruct (Z_le_gt_dec (Znth s norm) 0) as [LE|GT]; [exact LE|]. exfalso. rewrite Z.mod_small in K by lia.
        destruct (Z.ltb_spec 0 (Znth s norm)); destruct (Z.ltb_spec (Znth s norm) 9223372036854775808); cbn in K; try discriminate; lia. }
      assert (PN : place_n (Z.to_nat (Znth s norm)) (2^tl) (fse_tablestep (2^tl)) high s position cells = (cells, position))
        by (replace (Z.to_nat (Znth s norm)) with 0%nat by lia; reflexivity).
      eapply bf_slow_next; [exact HS | |].
      + intros LT. eapply KH; [exact PN | exact LT | exact I | exact HP].
      + intros EQ. eapply KE; [exact PN | exact EQ | exact I | exact HP].
    - assert (NGT : 0 < Znth s norm).
      { destruct (Z_le_gt_dec (Znth s norm) 0) as [LE|GT]; [|lia]. exfalso.
        destruct (Z.eq_dec (Znth s norm) 0) as [E0|NE0]; [rewrite E0 in K0; cbn in K0; lia|].
        assert (E1 : Znth s norm = -1) by lia. rewrite E1 in K1. cbn in K1. lia. }
      assert (HHR : 0 <= high < 2^tl).
      { pose proof (nsum_S norm tl TL9 s ltac:(unfold FseNCount.Zlength; lia)) as NS.
        pose proof (nsum_mono norm maxSV tl TL9 NLEN (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as NM.
        pose proof (nsum_nonneg norm maxSV tl TL9 NLEN s ltac:(lia)) as NN.
        pose proof (low_mono norm maxSV tl TL9 NLEN NGE 0 (maxSV + 1) ltac:(lia) ltac:(lia)) as LM0.
        change (FseReadSound.pws norm 0) with 0 in LM0. change (nsum norm 0) with 0 in LM0.
        unfold FseReadSound.pws in LM0. rewrite NSUM in LM0. lia. }
      zstep.
      eapply (bf_place_n t (Z.to_nat (Znth s norm - 1)) m1 h0 h1 w8 w16 cells symNext spread s 0 (Znth s norm) position high);
        [exact I | lia | lia | lia | lia | exact HP | exact HHR |].
      intros m2 cells' position' ya0 PN I2 HP2.
      replace (S (Z.to_nat (Znth s norm - 1))) with (Z.to_nat (Znth s norm)) in PN by lia.
      zstep.
      eapply bf_slow_next; [exact HS | |].
      + intros LT. eapply KH; [exact PN | exact LT | exact I2 | exact HP2].
      + intros EQ. eapply KE; [exact PN | exact EQ | exact I2 | exact HP2].
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow_loop : forall (t : seq_table) (f : nat) m1 h0 h1 w8 w16 cells symNext spread s position high
                              xra xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 xn,
    BFm h0 h1 w8 w16 cells symNext spread m1 ->
    0 <= s -> s + Z.of_nat (S f) = maxSV + 1 -> 0 <= position < 2^tl -> high + 1 = nsum norm (maxSV + 1) ->
    (forall m2 cells' p' yi ya0 yn,
       spread_slow (S f) norm (2^tl) (fse_tablestep (2^tl)) high s position cells = (cells', p') ->
       BFm h0 h1 w8 w16 cells' symNext spread m2 ->
       evt psegs (POST t) (STC 0x16a9c m2 xra (Z_to_bv 64 (maxSV + 1)) yi xs1 ya0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
                               (Z_to_bv 64 p') (Z_to_bv 64 (fse_tablestep (2^tl))) yn)) ->
    evt psegs (POST t) (STC 0x169f0 m1 xra (Z_to_bv 64 s) xi xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
                            (Z_to_bv 64 position) (Z_to_bv 64 (fse_tablestep (2^tl))) xn).
  Proof.
    intros t f. induction f as [|f IH]; intros until xn; intros I HS HSF HP HHN KONT.
    - eapply bf_slow_body; [exact I | lia | exact HP | exact HHN | |].
      + intros; exfalso; lia.
      + intros m2 cells' p' yi ya0 yn PN _ I2 HP2. eapply KONT; [| exact I2].
        cbn [spread_slow]. rewrite PN. reflexivity.
    - eapply bf_slow_body; [exact I | lia | exact HP | exact HHN | |].
      + intros m2 cells' p' yi ya0 yn PN LT I2 HP2.
        eapply (IH m2 h0 h1 w8 w16 cells' symNext spread (s + 1) p' high); [exact I2 | lia | lia | exact HP2 | exact HHN |].
        intros m3 cells'' p'' yi' ya0' yn' SS I3. eapply KONT; [| exact I3].
        change (spread_slow (S (S f)) norm (2^tl) (fse_tablestep (2^tl)) high s position cells)
          with (let '(c1, p1) := place_n (Z.to_nat (Znth s norm)) (2^tl) (fse_tablestep (2^tl)) high s position cells in
                spread_slow (S f) norm (2^tl) (fse_tablestep (2^tl)) high (s + 1) p1 c1).
        rewrite PN. exact SS.
      + intros; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_slow : forall (t : seq_table) m1 h0 h1 w8 w16 cells symNext spread high xra x6e xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 x29 x30 x31,
    BFm h0 h1 w8 w16 cells symNext spread m1 -> high + 1 = nsum norm (maxSV + 1) ->
    (forall m2 cells' p' yi ya0 yn,
       spread_slow (Z.to_nat (maxSV + 1)) norm (2^tl) (fse_tablestep (2^tl)) high 0 0 cells = (cells', p') ->
       BFm h0 h1 w8 w16 cells' symNext spread m2 ->
       evt psegs (POST t) (STC 0x16a9c m2 xra (Z_to_bv 64 (maxSV + 1)) yi xs1 ya0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high)
                               (Z_to_bv 64 p') (Z_to_bv 64 (fse_tablestep (2^tl))) yn)) ->
    evt psegs (POST t) (STC 0x169d0 m1 xra x6e (Z_to_bv 64 (2^tl / 8)) xs1 xa0 xs2 xs3 xs4 xs5 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 high) x29 x30 x31).
  Proof.
    intros until x31; intros I HHN KONT. open_bh HY.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    zstep. zstep. zstep. rewrite (srliw_val (2^tl) 1) by lia. rewrite (Z.mod_small (2^tl) 4294967296) by lia. change (2^1) with 2.
    zstep. zstep. zstep.
    replace (2^tl / 8 + 2^tl / 2 + 3) with (fse_tablestep (2^tl)) by (unfold fse_tablestep; lia).
    eapply (bf_slow_loop t (Z.to_nat maxSV) m1 h0 h1 w8 w16 cells symNext spread 0 0 high); [exact I | lia | lia | lia | exact HHN |].
    intros m2 cells' p' yi ya0 yn SS I2. eapply KONT; [| exact I2].
    replace (Z.to_nat (maxSV + 1)) with (S (Z.to_nat maxSV)) by lia. exact SS.
  Qed.
End C.
