(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdSeqTable ZdSeqBuild ZdSeqBuildThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdSeqBuildW2 ZdSeqBuildW3 ZdSeqBuildW4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_blk_iface RZ_bfse_defs seqH_kit seqH_kit_fse.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.


Section B.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DT NC BASE BITS W maxSV tl : Z) (k : seq_kind) (wlen : nat) (norm : list Z).
  Hypothesis HY : bf_hyps SPV lo DT NC BASE BITS W maxSV tl k wlen norm.
  Hypothesis AL : bf_al DT W NC BASE.
  Notation POST t := (bf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT W tl wlen lo m t).
  Notation ST pc mm xra x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 (SPV + -128)) gp tp x5 x6 x7 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation BFm := (BFU ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m SPV lo DT NC BASE BITS W tl k wlen norm).

  (* [comment removed for export] *)
  Notation STP pc mm xra xs0 xs1 xa0 xa2 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 (18446744073709551615 - W)) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (2^tl + -1)) xs0 xs1 xa0 (Z_to_bv 64 NC) xa2
        (Z_to_bv 64 BASE) (Z_to_bv 64 BITS) (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 8)) xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (18446744073709551615 - (DT + 8))) x29 x30 x31).
  Notation ST1 pc mm xra xa0 xa2 xs0 xs2 xs8 xs9 xs10 xs11 x29 x31 :=
    (STP pc mm xra xs0 (Z_to_bv 64 0) xa0 xa2 xs2 (Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 1) (Z_to_bv 64 65535)
         (Z_to_bv 64 (2^(tl + -1))) (Z_to_bv 64 (2 * (maxSV + 1))) xs8 xs9 xs10 xs11 x29 (Z_to_bv 64 (maxSV + 1)) x31).


  (* [comment removed for export] *)
  Notation ST2 pc mm xra xa0 xa2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 x30 x31 :=
    (STP pc mm xra (Z_to_bv 64 (18446744073709551615 - NC)) (Z_to_bv 64 9) xa0 xa2 (Z_to_bv 64 72340172838076673) (Z_to_bv 64 (W + 106))
         xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 x30 x31).

  Notation SVK s := (s * 72340172838076673).
  (* [comment removed for export] *)
  Notation ST2W pc mm xa0 xa2 xs xn x29 xpos :=
    (ST2 pc mm (Z_to_bv 64 (SVK xs ≫ 8)) xa0 xa2 (Z_to_bv 64 xs) (Z_to_bv 64 xn) (Z_to_bv 64 (SVK xs ≫ 56)) (Z_to_bv 64 (SVK xs ≫ 48))
         (Z_to_bv 64 (SVK xs ≫ 40)) (Z_to_bv 64 (SVK xs ≫ 32)) (Z_to_bv 64 (SVK xs ≫ 24)) (Z_to_bv 64 (SVK xs ≫ 16)) x29 (Z_to_bv 64 xpos)
         (Z_to_bv 64 (SVK xs))).

  (* [comment removed for export] *)
  Ltac spst SPRD i v :=
    lazymatch type of SPRD with u8arr ?segs ?mx ?A (map (Z_to_bv 8) ?buf) =>
      let a := cur_mem_addr in let SOK := fresh "SOK" in
      pose proof (u8arr_store_ok segs mx A _ i a SPRD ltac:(rewrite ?length_map, ?FseLemmas.Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
      zstep;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx (Z_to_bv 64 ?E) (le1 (Z_to_bv 64 ?x))) _) =>
        let S2 := fresh "SPRD" in
        assert (S2 : u8arr segs (write_to_mem mx (wa E) (le1 (Z_to_bv 64 x))) A (map (Z_to_bv 8) (Zupd i v buf)));
        [ replace (wa E) with (wa (A + i)) by (unfold wa; f_equal; lia);
          apply (u8arr_sb segs mx A buf i x v SPRD); [ rewrite ?FseLemmas.Zupd_length; lia | ]
        | clear SPRD; let X := base_var A in hide_not_mentioning X; store_done; unhide; rename S2 into SPRD ]
      end
    end.
  Ltac svb s :=
    lazymatch goal with
    | |- (Z.shiftr ?e ?kq) mod 256 = _ mod 256 =>
        let j := eval vm_compute in (kq / 8) in change kq with (8 * j); rewrite (sv_byte s j) by lia; symmetry; apply Z.mod_small; lia
    | |- ?e mod 256 = _ mod 256 =>
        change (e mod 256) with ((Z.shiftr e (8 * 0)) mod 256); rewrite (sv_byte s 0) by lia; symmetry; apply Z.mod_small; lia
    end.

  (* [comment removed for export] *)
  Lemma bf_lay_inner : forall (t : seq_table) (j : nat) m1 h0 h1 cells symNext spread s pos n i,
    BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext spread m1 -> 0 <= s <= 52 -> 0 <= pos -> 8 <= i < n ->
    pos + n + 7 <= zlenF spread -> n <= i + 8 * Z.of_nat (S j) ->
    (forall m2 ya0 ya2, BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext (lay_more (S j) spread pos s i n) m2 ->
       evt usegs (POST t) (ST2W 0x16fbc m2 ya0 ya2 s n (Z_to_bv 64 (18446744073709551615 - (W + 106 + pos))) pos)) ->
    evt usegs (POST t) (ST2W 0x1704c m1 (Z_to_bv 64 (W + 106 + pos + i)) (Z_to_bv 64 i) s n (Z_to_bv 64 (18446744073709551615 - (W + 106 + pos))) pos).
  Proof.
    intros t j. induction j as [|j IH]; intros until i; intros I HS HP HI HL HF KONT; open_bh HY; open_bfu I.
    all: destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    all: assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    all: assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    all: unfold FseNCount.Zlength in *.
    all: zstep; uck.
    all: spst SPRD (pos + i + 4) s; [svb s|].
    all: spst SPRD (pos + i + 5) s; [svb s|].
    all: spst SPRD (pos + i + 6) s; [svb s|].
    all: spst SPRD (pos + i + 7) s; [svb s|].
    all: spst SPRD (pos + i) s; [svb s|].
    all: spst SPRD (pos + i + 1) s; [svb s|].
    all: spst SPRD (pos + i + 2) s; [svb s|].
    all: spst SPRD (pos + i + 3) s; [svb s|].
    all: fold (wr8m spread (pos + i) s) in SPRD; rewrite (wr8m_eq spread (pos + i) s) in SPRD by (unfold FseNCount.Zlength; lia).
    all: assert (SPLEN' : zlenF (write8 spread (pos + i) s) = Z.of_nat wlen - 106) by (unfold FseNCount.Zlength; rewrite write8_length; exact SPLEN).
    all: zstep; zstep; zstep; if_cases K; zify_cond K.
    - exfalso; lia.
    - zstep. eapply KONT. cbn [lay_more]. replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia). close_bfu.
    - replace (W + 106 + pos + i + 8) with (W + 106 + pos + (i + 8)) by lia.
      eapply (IH _ h0 h1 cells symNext (write8 spread (pos + i) s) s pos n (i + 8));
        [close_bfu | exact HS | exact HP | lia | unfold FseNCount.Zlength; rewrite write8_length; lia | lia |].
      intros m2 ya0 ya2 I2. eapply KONT.
      replace (lay_more (S (S j)) spread pos s i n) with (lay_more (S j) (write8 spread (pos + i) s) pos s (i + 8) n)
        by (cbn [lay_more]; replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      exact I2.
    - zstep. eapply KONT.
      replace (lay_more (S (S j)) spread pos s i n) with (write8 spread (pos + i) s)
        by (cbn [lay_more]; replace (i <? n) with true by (symmetry; apply Z.ltb_lt; lia);
            replace (i + 8 <? n) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      close_bfu.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_lay_next : forall (t : seq_table) m1 h0 h1 cells symNext spread s pos n xra xa0 xa2 xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext spread m1 ->
    0 <= s <= maxSV -> 0 <= pos -> 0 <= n -> pos + n <= 2^tl ->
    (s + 1 < maxSV + 1 -> evt usegs (POST t)
       (ST2 0x16fd0 m1 xra (Z_to_bv 64 (s + 1)) (Z_to_bv 64 maxSV) (Z_to_bv 64 s) (Z_to_bv 64 n) xs6 xs7 xs8 xs9 xs10 xs11 x29
            (Z_to_bv 64 (pos + n)) (Z_to_bv 64 (SVK (s + 1))))) ->
    (s + 1 = maxSV + 1 -> evt usegs (POST t)
       (ST2 0x17108 m1 xra (Z_to_bv 64 (s + 1)) (Z_to_bv 64 maxSV) (Z_to_bv 64 s) (Z_to_bv 64 n) xs6 xs7 xs8 xs9 xs10 xs11 x29
            (Z_to_bv 64 (pos + n)) (Z_to_bv 64 (SVK (s + 1))))) ->
    evt usegs (POST t)
       (ST2 0x16fbc m1 xra xa0 xa2 (Z_to_bv 64 s) (Z_to_bv 64 n) xs6 xs7 xs8 xs9 xs10 xs11 x29 (Z_to_bv 64 pos) (Z_to_bv 64 (SVK s))).
  Proof.
    intros until x29; intros I HS HP HN HPN KH KE.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    pose proof I as I'. open_bfu I'.
    zstep. zstep. rewrite (swrap32_small (s + 1)) by lia. zstep.
    replace (s * 72340172838076673 + 72340172838076673) with (SVK (s + 1)) by lia.
    zstep. zstep. if_cases K; zify_cond K.
    - apply KE. lia.
    - apply KH. lia.
  Qed.
  (* [comment removed for export] *)
  Definition lay_step (s pos : Z) (spread : list Z) : list Z :=
    lay_more (Z.to_nat (Znth s norm / 8 + 1)) (write8 spread pos s) pos s 8 (Znth s norm).

  (* [comment removed for export] *)
  Lemma bf_lay_blocks : forall (t : seq_table) m1 h0 h1 cells symNext spread1 s pos n xa0 xa2,
    BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext spread1 m1 ->
    0 <= s <= 52 -> 0 <= pos -> 9 <= n -> pos + n + 7 <= zlenF spread1 ->
    (forall m2 ya0 ya2 y29, BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext (lay_more (Z.to_nat (n / 8 + 1)) spread1 pos s 8 n) m2 ->
       evt usegs (POST t) (ST2W 0x16fbc m2 ya0 ya2 s n y29 pos)) ->
    evt usegs (POST t) (ST2W 0x17038 m1 xa0 xa2 s n (Z_to_bv 64 (W + 106 + pos)) pos).
  Proof.
    intros until xa2; intros I HS HP HN HL KONT. open_bh HY.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    pose proof I as I'. open_bfu I'. unfold FseNCount.Zlength in *.
    zstep. uck.
    zstep. rewrite (zb_lxor_ones (W + 106 + pos)) by lia.
    zstep. zstep. zstep.
    replace (W + 114 + pos) with (W + 106 + pos + 8) by lia.
    assert (EJ : Z.to_nat (n / 8 + 1) = S (Z.to_nat (n / 8))) by (Z.div_mod_to_equations; lia).
    eapply (bf_lay_inner t (Z.to_nat (n / 8)) m1 h0 h1 cells symNext spread1 s pos n 8); [exact I | exact HS | exact HP | lia | exact HL | |].
    - rewrite Nat2Z.inj_succ, Z2Nat.id by (apply Z.div_pos; lia). Z.div_mod_to_equations; lia.
    - intros m2 ya0 ya2 I2. apply KONT. rewrite EJ. exact I2.
  Qed.
  (* [comment removed for export] *)
  Lemma bf_lay_body : forall (t : seq_table) m1 h0 h1 cells symNext spread s pos xra xa2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext spread m1 ->
    0 <= s <= maxSV -> 0 <= pos -> 0 <= Znth s norm -> pos + Znth s norm <= 2^tl ->
    (forall m2 yra ya2 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29, s + 1 < maxSV + 1 ->
       BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext (lay_step s pos spread) m2 ->
       evt usegs (POST t)
         (ST2 0x16fd0 m2 yra (Z_to_bv 64 (s + 1)) ya2 (Z_to_bv 64 s) ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 (Z_to_bv 64 (pos + Znth s norm))
              (Z_to_bv 64 (SVK (s + 1))))) ->
    (forall m2 yra ya2 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29, s + 1 = maxSV + 1 ->
       BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext (lay_step s pos spread) m2 ->
       evt usegs (POST t)
         (ST2 0x17108 m2 yra (Z_to_bv 64 (s + 1)) ya2 (Z_to_bv 64 s) ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 (Z_to_bv 64 (pos + Znth s norm))
              (Z_to_bv 64 (SVK (s + 1))))) ->
    evt usegs (POST t)
      (ST2 0x16fd0 m1 xra (Z_to_bv 64 s) xa2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 (Z_to_bv 64 pos) (Z_to_bv 64 (SVK s))).
  Proof.
    intros until x29; intros I HS HP HN HPN KH KE; open_bh HY; open_bfu I. pose proof AL as (DTA & WAL & NCA & BASEA).
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    unfold FseNCount.Zlength in *.
    set (n := Znth s norm) in *.
    zstep. zstep. zstep. rewrite (zext32_sh31 s) by lia.
    zstep. uck. zstep. zstep. zstep. uck. zstep. zstep. uck.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u16_znth usegs m1 NC norm s a NCB ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. fold n. rewrite (sx16_short n) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    spst SPRD (pos + 4) s; [svb s|].
    spst SPRD (pos + 5) s; [svb s|].
    spst SPRD (pos + 6) s; [svb s|].
    spst SPRD (pos + 7) s; [svb s|].
    spst SPRD pos s; [svb s|].
    spst SPRD (pos + 1) s; [svb s|].
    spst SPRD (pos + 2) s; [svb s|].
    spst SPRD (pos + 3) s; [svb s|].
    fold (wr8m spread pos s) in SPRD; rewrite (wr8m_eq spread pos s) in SPRD by (unfold FseNCount.Zlength; lia).
    assert (SPLEN' : zlenF (write8 spread pos s) = Z.of_nat wlen - 106) by (unfold FseNCount.Zlength; rewrite write8_length; exact SPLEN).
    zstep. if_cases K; zify_cond K.
    - rewrite (signed_lit n) in K by lia.
      assert (LS : lay_step s pos spread = write8 spread pos s).
      { unfold lay_step. fold n. destruct (Z.to_nat (n / 8 + 1)) as [|f0]; cbn [lay_more]; [reflexivity|].
        replace (8 <? n) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      eapply (bf_lay_next t _ h0 h1 cells symNext (write8 spread pos s) s pos n); [close_bfu | exact HS | exact HP | exact HN | exact HPN | |].
      + intros LT. eapply KH; [exact LT|]. rewrite LS. close_bfu.
      + intros EQ. eapply KE; [exact EQ|]. rewrite LS. close_bfu.
    - rewrite (signed_lit n) in K by lia.
      (* [comment removed for export] *)
      eapply (bf_lay_blocks t _ h0 h1 cells symNext (write8 spread pos s) s pos n);
        [close_bfu | lia | exact HP | lia | unfold FseNCount.Zlength; rewrite write8_length; lia |].
      (* [comment removed for export] *)
      intros m2 ya0 ya2 y29 I2.
      assert (I3 : BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext (lay_step s pos spread) m2) by (unfold lay_step; fold n; exact I2).
      eapply (bf_lay_next t m2 h0 h1 cells symNext (lay_step s pos spread) s pos n); [exact I3 | exact HS | exact HP | exact HN | exact HPN | |].
      + intros LT. eapply KH; [exact LT | exact I3].
      + intros EQ. eapply KE; [exact EQ | exact I3].
  Qed.

  (* [comment removed for export] *)
  Lemma bf_nolow : nsum norm (maxSV + 1) = 2^tl -> forall i, 0 <= i <= maxSV -> 0 <= Znth i norm.
  Proof.
    intros HNL i Hi. open_bh HY. destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    pose proof (low_step norm maxSV tl TL9 NLEN NGE i Hi) as LS.
    pose proof (low_mono norm maxSV tl TL9 NLEN NGE 0 i ltac:(lia) ltac:(lia)) as L0.
    pose proof (low_mono norm maxSV tl TL9 NLEN NGE (i + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as L1.
    change (FseReadSound.pws norm 0) with 0 in L0. change (nsum norm 0) with 0 in L0.
    unfold FseReadSound.pws in L1 at 2. rewrite NSUM, HNL in L1.
    pose proof (NGE i Hi). destruct (Z.eqb_spec (Znth i norm) (-1)); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_lay_loop : forall (t : seq_table) (f : nat) m1 h0 h1 cells symNext spread s pos xra xa2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext spread m1 ->
    0 <= s -> s + Z.of_nat (S f) = maxSV + 1 -> pos = nsum norm s -> nsum norm (maxSV + 1) = 2^tl ->
    (forall m2 spread' pos' yra ya0 ya2 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 y31,
       lay_symbols (S f) norm s pos spread = (spread', pos') ->
       BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells symNext spread' m2 ->
       evt usegs (POST t)
         (ST2 0x17108 m2 yra ya0 ya2 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 (Z_to_bv 64 pos') y31)) ->
    evt usegs (POST t)
      (ST2 0x16fd0 m1 xra (Z_to_bv 64 s) xa2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 (Z_to_bv 64 pos) (Z_to_bv 64 (SVK s))).
  Proof.
    intros t f. induction f as [|f IH]; intros until x29; intros I HS HSF HPOS HNL KONT.
    all: open_bh HY; destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    all: pose proof (bf_nolow HNL s ltac:(lia)) as HN.
    all: pose proof (nsum_S norm tl TL9 s ltac:(unfold FseNCount.Zlength in *; lia)) as NS.
    all: pose proof (nsum_mono norm maxSV tl TL9 NLEN (s + 1) (maxSV + 1) ltac:(lia) ltac:(lia)) as NM.
    all: pose proof (nsum_nonneg norm maxSV tl TL9 NLEN s ltac:(lia)) as NN.
    all: assert (HPN : pos + Znth s norm <= 2^tl) by lia.
    - eapply bf_lay_body; [exact I | lia | lia | exact HN | exact HPN | |].
      + intros; exfalso; lia.
      + intros m2 yra ya2 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 _ I2. eapply KONT; [| exact I2]. reflexivity.
    - eapply bf_lay_body; [exact I | lia | lia | exact HN | exact HPN | |].
      + intros m2 yra ya2 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 LT I2.
        eapply (IH m2 h0 h1 cells symNext (lay_step s pos spread) (s + 1) (pos + Znth s norm)); [exact I2 | lia | lia | lia | exact HNL |].
        intros m3 spread' pos' zra za0 za2 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 z29 z31 LSY I3. eapply KONT; [| exact I3].
        exact LSY.
      + intros; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Notation STF pc mm xra xa0 xs xpos xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29 :=
    (ST pc mm xra (Z_to_bv 64 (18446744073709551615 - W)) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (2^tl + -1))
        (Z_to_bv 64 (2 * fse_tablestep (2^tl))) (Z_to_bv 64 (W + 107)) xa0 xs xpos (Z_to_bv 64 BASE) (Z_to_bv 64 BITS)
        (Z_to_bv 64 tl) (Z_to_bv 64 W) (Z_to_bv 64 (DT + 8)) xs2 (Z_to_bv 64 (W + 106)) xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11
        (Z_to_bv 64 (18446744073709551615 - (DT + 8))) x29 (Z_to_bv 64 (18446744073709551615 - (W + 106))) (Z_to_bv 64 (fse_tablestep (2^tl)))).

  (* [comment removed for export] *)
  Lemma bf_fast_loop : forall (t : seq_table) (f : nat) m1 h0 h1 w8 w16 cells symNext spread s position xra xa0 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29,
    BFm h0 h1 w8 w16 cells symNext spread m1 -> Forall (fun v => 0 <= v < 256) spread ->
    0 <= s -> s + 2 * Z.of_nat (S f) = 2^tl -> 0 <= position < 2^tl ->
    (forall m2 cells' p' ya0 ys y29,
       place_fast (S f) (2^tl) (fse_tablestep (2^tl)) spread s position cells = (cells', p') ->
       BFm h0 h1 w8 w16 cells' symNext spread m2 ->
       evt usegs (POST t) (STF 0x17180 m2 xra ya0 ys (Z_to_bv 64 p') xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 y29)) ->
    evt usegs (POST t) (STF 0x1712c m1 xra xa0 (Z_to_bv 64 s) (Z_to_bv 64 position) xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x29).
  Proof.
    intros t f. induction f as [|f IH]; intros until x29; intros I SB HS HSF HP KONT; open_bh HY; open_bfu I.
    all: destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    all: assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    all: assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    all: unfold FseNCount.Zlength in *.
    all: assert (STEPR : 0 <= fse_tablestep (2^tl) < 1048576) by (unfold fse_tablestep; Z.div_mod_to_equations; lia).
    all: set (step := fse_tablestep (2^tl)) in *.
    all: pose proof (Forall_Znth _ _ s SB ltac:(lia)) as B0; pose proof (Forall_Znth _ _ (s + 1) SB ltac:(lia)) as B1; cbv beta in B0, B1.
    all: assert (LM : forall x, 0 <= x -> Z.land x (2^tl + -1) = x mod 2^tl)
           by (intros x Hx; replace (2^tl + -1) with (Z.ones tl) by (rewrite Z.ones_equiv; lia); apply Z.land_ones; lia).
    all: zstep; uck.
    all: zstep; rewrite (LM position) by lia.
    all: assert (Q0 : 0 <= position mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; rewrite (Z.shiftl_mul_pow2 (position mod 2^tl) 3) by lia; change (2^3) with 8.
    all: zstep; uck; zstep.
    all: lazymatch goal with |- _ => let a := cur_mem_addr in
           pose proof (u8arr_read usegs m1 (W + 106) _ s _ a SPRD (nth_error_map_Znth (Z_to_bv 8) spread s ltac:(lia)) ltac:(lia) ltac:(addr_tac)) as RD end.
    all: zstep; cbv beta; rewrite (byte_lit (Znth s spread)) by lia.
    all: zstep.
    all: cst CEL (position mod 2^tl) 4 4%nat cellsB_store_base (2^32).
    all: rewrite (Z.mod_small (Znth s spread) (2^32)) in CEL by lia.
    all: rewrite <- (set_base_as_set_cell cells (position mod 2^tl) (Znth s spread)) in CEL by (unfold FseNCount.Zlength; lia).
    all: set (c1 := set_base (position mod 2^tl) (Znth s spread) cells) in *.
    all: assert (CLEN1 : Z.of_nat (length c1) = 2^tl) by (subst c1; rewrite set_base_length; exact CLEN).
    all: zstep; uck.
    all: zstep; zstep; rewrite (LM (position + step)) by lia.
    all: assert (Q1 : 0 <= (position + step) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; rewrite (Z.shiftl_mul_pow2 ((position + step) mod 2^tl) 3) by lia; change (2^3) with 8.
    all: zstep; uck; zstep.
    all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => let a := cur_mem_addr in
           pose proof (u8arr_read usegs mx (W + 106) _ (s + 1) _ a SPRD (nth_error_map_Znth (Z_to_bv 8) spread (s + 1) ltac:(lia)) ltac:(lia) ltac:(addr_tac)) as RD2 end.
    all: zstep; cbv beta; rewrite (byte_lit (Znth (s + 1) spread)) by lia.
    all: zstep; zstep; zstep.
    all: cst CEL ((position + step) mod 2^tl) 4 4%nat cellsB_store_base (2^32).
    all: rewrite (Z.mod_small (Znth (s + 1) spread) (2^32)) in CEL by lia.
    all: rewrite <- (set_base_as_set_cell c1 ((position + step) mod 2^tl) (Znth (s + 1) spread)) in CEL by (unfold FseNCount.Zlength; lia).
    all: set (c2 := set_base ((position + step) mod 2^tl) (Znth (s + 1) spread) c1) in *.
    all: assert (CLEN2 : zlenF c2 = 2^tl) by (unfold FseNCount.Zlength; subst c2; rewrite set_base_length; exact CLEN1).
    all: zstep; rewrite (LM (position + 2 * step)) by lia.
    all: assert (Q2 : 0 <= (position + 2 * step) mod 2^tl < 2^tl) by (apply Z.mod_pos_bound; lia).
    all: zstep; if_cases K; zify_cond K.
    - exfalso; lia.
    - eapply KONT; [cbn [place_fast]; reflexivity|]. fold step. fold c1. fold c2. close_bfu.
    - eapply (IH _ h0 h1 w8 w16 c2 symNext spread (s + 2) ((position + 2 * step) mod 2^tl)); [close_bfu | exact SB | lia | lia | exact Q2 |].
      intros m2 cells' p' ya0 ys y29 PF I2. eapply KONT; [| exact I2].
      cbn [place_fast]. fold step. fold c1. fold c2. exact PF.
    - exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bf_fast : forall (t : seq_table) m1 h0 h1 w8 cells symNext spread xra xs0 xs1 xa0 xa2 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x31,
    BFm h0 h1 w8 (Z_to_bv 64 maxSV) cells symNext spread m1 -> Forall (fun v => 0 <= v < 256) spread -> nsum norm (maxSV + 1) = 2^tl ->
    (forall m2 spread1 pos1 cells2 p2 yra ya0 ys ys2 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29,
       lay_symbols (Z.to_nat (maxSV + 1)) norm 0 0 spread = (spread1, pos1) ->
       place_fast (Z.to_nat (2^tl / 2)) (2^tl) (fse_tablestep (2^tl)) spread1 0 0 cells = (cells2, p2) ->
       BFm h0 h1 (Z_to_bv 64 (W + 114)) (Z_to_bv 64 maxSV) cells2 symNext spread1 m2 ->
       evt usegs (POST t) (STF 0x17180 m2 yra ya0 ys (Z_to_bv 64 p2) ys2 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29)) ->
    evt usegs (POST t) (STP 0x16f80 m1 xra xs0 xs1 xa0 xa2 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 (2^tl + -1))
                            (Z_to_bv 64 (maxSV + 1)) x31).
  Proof.
    intros until x31; intros I SB HNL KONT. open_bh HY. pose proof I as I'. open_bfu I'.
    destruct (bf_size_rng _ _ _ _ _ _ _ _ _ _ _ _ HY) as (TL9 & SZ & MSV52).
    assert (LBASE : Z.of_nat (length (kind_base k)) <= 53) by (destruct k; vm_compute; discriminate).
    assert (LBITS : Z.of_nat (length (kind_bits k)) <= 53) by (destruct k; vm_compute; discriminate).
    unfold FseNCount.Zlength in *.
    zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    zstep. uck. zstep. zstep. zstep.
    zstep. rewrite (zb_lxor_ones NC) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    eapply (bf_lay_loop t (Z.to_nat maxSV) _ h0 h1 cells symNext spread 0 0); [close_bfu | lia | lia | reflexivity | exact HNL |].
    intros mm2 spread1 pos1 yra ya0 ya2 ys4 ys5 ys6 ys7 ys8 ys9 ys10 ys11 y29 y31 LSY I2.
    replace (S (Z.to_nat maxSV)) with (Z.to_nat (maxSV + 1)) in LSY by lia.
    assert (SB1 : Forall (fun v => 0 <= v < 256) spread1).
    { pose proof (lay_symbols_bytes norm (Z.to_nat (maxSV + 1)) 0 0 spread ltac:(lia) ltac:(lia) SB) as LB. rewrite LSY in LB. exact LB. }
    clear HDR CEL CLEN SNX SNLEN SPRD SPLEN NCB BASEB BITSB STK FR MI MU WM. open_bfu I2.
    zstep. zstep.
    zstep. rewrite (srliw_val (2^tl) 1) by lia.
    zstep. rewrite (srliw_val (2^tl) 3) by lia. rewrite (Z.mod_small (2^tl) 4294967296) by lia. change (2^1) with 2. change (2^3) with 8.
    zstep. rewrite (zb_lxor_ones (W + 106)) by lia.
    zstep. zstep. rewrite (swrap32_small (2^tl / 8 + 2^tl / 2 + 3)) by (Z.div_mod_to_equations; lia).
    replace (2^tl / 8 + 2^tl / 2 + 3) with (fse_tablestep (2^tl)) by (unfold fse_tablestep; lia).
    assert (STEPR : 0 <= fse_tablestep (2^tl) < 1048576) by (unfold fse_tablestep; Z.div_mod_to_equations; lia).
    zstep. rewrite ?(Z.mod_small (fse_tablestep (2^tl)) 18446744073709551616) by lia.
    rewrite (Z.shiftl_mul_pow2 (fse_tablestep (2^tl)) 1) by lia. replace (fse_tablestep (2^tl) * 2^1) with (2 * fse_tablestep (2^tl)) by lia.
    zstep.
    assert (EVEN : 2 * (2^tl / 2) = 2^tl).
    { assert (E2 : 2^tl = 2^(tl - 1) * 2) by (replace tl with (Z.succ (tl - 1)) at 1 by lia; rewrite Z.pow_succ_r by lia; lia).
      rewrite E2 at 1. rewrite Z.div_mul by lia. lia. }
    eapply (bf_fast_loop t (Z.to_nat (2^tl / 2 - 1)) _ h0 h1 _ _ cells symNext spread1 0 0); [close_bfu | exact SB1 | lia | | lia |].
    - assert (1 <= 2^tl / 2) by (Z.div_mod_to_equations; lia). lia.
    - intros mm3 cells2 p2 za0 zs z29 PF I3.
      replace (S (Z.to_nat (2^tl / 2 - 1))) with (Z.to_nat (2^tl / 2)) in PF by (assert (1 <= 2^tl / 2) by (Z.div_mod_to_equations; lia); lia).
      eapply KONT; [exact LSY | exact PF | exact I3].
  Qed.
End B.
