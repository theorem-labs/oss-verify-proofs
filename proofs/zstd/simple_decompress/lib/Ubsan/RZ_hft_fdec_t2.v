(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_hft_fdec_epi RZ_fse_decnf_kit RZ_fse_decf_kit fse_kit_dsym.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section T2.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis LOSU : lo <= SPV - 192.
  Hypothesis SPA : SPV mod 16 = 0.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis WKR0 : 0 <= wksz.
  Hypothesis DSYM : fse_dsym_stmt.
  Hypothesis DSYMF : fse_dsymf_stmt.
  Hypothesis FAST1 : fast = 1.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FDCm := (FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).
  Notation STE pc mm x1 st1 st2 bc j P cont x10 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j))
       x10 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
       (Z_to_bv 64 P) (Z_to_bv 64 (DST + cap)) x19 x20 x21 x22 x23 x24 x25 x26 x27 cont x29 x30 x31).

  (* [comment removed for export] *)
  Notation STT pc mm x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont :=
    (STF pc mm x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j0))
       (Z_to_bv 64 (-70)) (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
       (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 (j0 - j)) (Z_to_bv 64 64) (Z_to_bv 64 1) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j))
       x24 x25 x26 x27 cont (Z_to_bv 64 (DST + cap + -2)) (Z_to_bv 64 1) (Z_to_bv 64 2)).

  Lemma fd2_t_err : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    evt usegs POST (STF 0x2b964 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (-70)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I. apply fdcu_fdu in I.
    replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 18446744073709551546) by (apply bv_eq; reflexivity).
    eapply fd_epi; try eassumption; first [lia | left; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Definition t2_KH (pad : list byte) (j0 j : Z) : Prop :=
    forall m2 out' st1' st2' bc' ptr' cont' y1 y24 y25 y26 y27,
      FDCm out' st1' st2' cont' bc' pad ptr' m2 -> 0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> fbit_ok SRCI ni bc' ptr' -> bc' <= 100 -> j + 4 <= cap ->
      evt usegs POST (STT 0x2b9d8 m2 y1 st1' st2' bc' j0 (j + 2) ptr' y24 y25 y26 y27 cont').

  (* [comment removed for export] *)
  Lemma fd2_t_j2 : forall m1 out x1 st1 st2 bc j0 j ptr cont pad x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 ->
    (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2b9c4 m1 x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I S1 S2 BCR PV HJ HJC KH. open_fh HY.
    zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K.
    - eapply fd2_t_err; exact I.
    - replace (j0 - j + -2) with (j0 - (j + 2)) by lia.
      replace (DST + j + 3) with (DST + (j + 2) + 1) by lia.
      replace (DST + j + 2) with (DST + (j + 2)) by lia.
      unfold t2_KH in KH.
      eapply KH; [exact I | exact S1 | exact S2 | unfold fbit_ok; split; [lia | intros _; exact PV] | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_rB_load : forall m1 out x1 st1 st2 bc bc' j0 j ptr ptr' cont pad x25 x26 x27 x28,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc' <= 64 -> 4096 <= ptr < 2^47 ->
    (ptr' = SRCI \/ (8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8)) -> ptr' + 8 <= SRCI + ni -> 0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2bc14 m1 x1 st1 st2 bc' j0 j ptr (Z_to_bv 64 ptr') x25 x26 x27 x28).
  Proof.
    intros until x28; intros I S1 S2 BCR P0 PV PH HJ HJC KH. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep.
    zstep. zchk.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
    zstep. zstep. zstep.
    eapply fd2_t_j2; [close_fdcu | exact S1 | exact S2 | exact BCR | exact PV | exact HJ | exact HJC | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_rB : forall m1 out x1 st1 st2 bc j0 j ptr cont pad x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 ->
    (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2bb94 m1 x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I S1 S2 BCR PV HJ HJC KH. open_fh HY. pose proof I as I0.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
      assert (QR : 0 <= bc / 8 <= 8 /\ 0 <= bc mod 8 <= 7) by (clear - BCR; Z.div_mod_to_equations; lia).
      remember (bc / 8) as q eqn:EQ. clear EQ.
      zstep. zchk.
      zstep. zstep. zstep. zstep.
      zstep. zchk.
      zstep. rnorm.
      zstep. replace (Z.land bc 7) with (bc mod 8) by (symmetry; apply land_7).
      remember (bc mod 8) as r eqn:ER. clear ER.
      eapply (fd2_t_rB_load _ out _ st1 st2 bc _ j0 j ptr _ cont pad); [exact I0 | exact S1 | exact S2 | lia | lia | right; lia | lia | exact HJ | exact HJC | exact KH].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply fd2_t_j2; [exact I0 | exact S1 | exact S2 | exact BCR | exact PV | exact HJ | exact HJC | exact KH].
      + (* [comment removed for export] *)
        zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR; Z.div_mod_to_equations; lia).
        remember (bc / 8) as q eqn:EQ. clear EQ.
        zstep. zchk.
        zstep. zstep. zstep. zstep.
        zstep. zchk.
        zstep. rnorm.
        zstep. if_cases K3; zify_cond K3.
        * zstep. zstep. rnorm.
          zstep. zchk.
          zstep. zstep. zstep.
          zstep. zchk.
          zstep. rnorm.
          zstep. rnorm.
          zstep. rewrite swrap32_small by lia.
          zstep.
          eapply (fd2_t_rB_load _ out _ st1 st2 bc _ j0 j ptr _ cont pad); [exact I0 | exact S1 | exact S2 | lia | lia | right; lia | lia | exact HJ | exact HJC | exact KH].
        * zstep. rnorm.
          zstep. zstep. rnorm.
          zstep. zchk.
          zstep. zstep. zstep.
          zstep. zchk.
          zstep. rnorm.
          zstep. rnorm.
          zstep. rewrite swrap32_small by lia.
          zstep.
          eapply (fd2_t_rB_load _ out _ st1 st2 bc _ j0 j ptr _ cont pad); [exact I0 | exact S1 | exact S2 | lia | lia | left; lia | lia | exact HJ | exact HJC | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_mid : forall m1 out x1 st1 st2 bc j0 j ptr cont pad x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 ->
    (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2bb2c m1 x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I S1 S2 BCR PV HJ HJC KH. open_fh HY. pose proof I as I0. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. if_cases K; zify_cond K.
    - eapply fd2_t_err; exact I0.
    - destruct (fd_cell tl fast tb st2 TBL ltac:(lia) S2) as (NB2 & NB2f & NX2a & NX2b & SY2 & B20 & B21). specialize (NB2f FAST1).
      pose proof (fc_hi_lt tb st2 ltac:(lia) ltac:(lia)) as HI2.
      zstep. zstep. zstep.
      zstep. zchk.
      zstep. zstep.
      zstep. zchk.
      zstep. zchk.
      zshl. ldhi CELB DT tb st2.
      ldnx CELB DT tb st2.
      zstep.
      zstep. rnorm.
      zstep. rnorm. rewrite (hi_or (fc_hi tb st2) (fc_nx tb st2)) by lia.
      zstep. rnorm. rewrite (hi_nb tb st2) by lia.
      zstep.
      zstep. rewrite swrap32_small by lia.
      set (bc2 := fc_nb tb st2 + bc) in *. assert (BC2 : 0 <= bc2 <= 73) by (unfold bc2; lia). clearbody bc2.
      zstep.
      lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => set (b2 := e) end end.
      assert (B2R : 0 <= b2 < 2^(fc_nb tb st2)) by (apply fast_bits_lt; [apply Z.mod_pos_bound; lia | lia]). clearbody b2.
      zstep.
      zstep. rnorm. rewrite (hi_and (fc_hi tb st2) (fc_nx tb st2)) by lia.
      zstep. set (st2a := b2 + fc_nx tb st2) in *. assert (S2a : 0 <= st2a < 2^tl) by (unfold st2a; lia). clearbody st2a.
      zstep.
      zstep. zchk.
      zstep.
      outst OUT OLEN.
      zstep. if_cases K2; zify_cond K2.
      + eapply fd2_finB with (st1 := st1) (st2 := st2a) (cont := cont) (bc := bc2) (pad := pad) (ptr := ptr); try eassumption; first [lia | close_fdcu].
      + eapply (fd2_t_rB _ _ _ st1 st2a bc2 j0 j ptr cont pad); [close_fdcu | exact S1 | exact S2a | lia | exact PV | exact HJ | exact HJC | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_rA_load : forall m1 out x1 st1 st2 bc bc' j0 j ptr ptr' cont pad x25 x26 x27 x28,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc' <= 64 -> 4096 <= ptr < 2^47 ->
    (ptr' = SRCI \/ (8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8)) -> ptr' + 8 <= SRCI + ni -> 0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2bac0 m1 x1 st1 st2 bc' j0 j ptr (Z_to_bv 64 ptr') x25 x26 x27 x28).
  Proof.
    intros until x28; intros I S1 S2 BCR P0 PV PH HJ HJC KH. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep.
    zstep. zchk.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
    zstep. zstep.
    eapply fd2_t_mid; [close_fdcu | exact S1 | exact S2 | exact BCR | exact PV | exact HJ | exact HJC | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_rA : forall m1 out x1 st1 st2 bc j0 j ptr cont pad x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 ->
    (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2ba40 m1 x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I S1 S2 BCR PV HJ HJC KH. open_fh HY. pose proof I as I0.
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
      assert (QR : 0 <= bc / 8 <= 8 /\ 0 <= bc mod 8 <= 7) by (clear - BCR; Z.div_mod_to_equations; lia).
      remember (bc / 8) as q eqn:EQ. clear EQ.
      zstep. zchk.
      zstep. zstep. zstep. zstep.
      zstep. zchk.
      zstep. rnorm.
      zstep. replace (Z.land bc 7) with (bc mod 8) by (symmetry; apply land_7).
      remember (bc mod 8) as r eqn:ER. clear ER.
      eapply (fd2_t_rA_load _ out _ st1 st2 bc _ j0 j ptr _ cont pad); [exact I0 | exact S1 | exact S2 | lia | lia | right; lia | lia | exact HJ | exact HJC | exact KH].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply fd2_t_mid; [exact I0 | exact S1 | exact S2 | exact BCR | exact PV | exact HJ | exact HJC | exact KH].
      + (* [comment removed for export] *)
        zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR; Z.div_mod_to_equations; lia).
        remember (bc / 8) as q eqn:EQ. clear EQ.
        zstep. zchk.
        zstep. zstep. zstep. zstep.
        zstep. zchk.
        zstep. rnorm.
        zstep. if_cases K3; zify_cond K3.
        * zstep. zstep. rnorm.
          zstep. zchk.
          zstep. zstep. zstep.
          zstep. zchk.
          zstep. rnorm.
          zstep. rnorm.
          zstep. rewrite swrap32_small by lia.
          zstep.
          eapply (fd2_t_rA_load _ out _ st1 st2 bc _ j0 j ptr _ cont pad); [exact I0 | exact S1 | exact S2 | lia | lia | right; lia | lia | exact HJ | exact HJC | exact KH].
        * zstep. rnorm.
          zstep. zstep. rnorm.
          zstep. zchk.
          zstep. zstep. zstep.
          zstep. zchk.
          zstep. rnorm.
          zstep. rnorm.
          zstep. rewrite swrap32_small by lia.
          zstep.
          eapply (fd2_t_rA_load _ out _ st1 st2 bc _ j0 j ptr _ cont pad); [exact I0 | exact S1 | exact S2 | lia | lia | left; lia | lia | exact HJ | exact HJC | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_head : forall m1 out x1 st1 st2 bc j0 j ptr cont pad x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr -> bc <= 100 ->
    0 <= j0 <= j -> j + 2 <= cap -> t2_KH pad j0 j ->
    evt usegs POST (STT 0x2b9d8 m1 x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I S1 S2 (BCR & BOK) B100 HJ HJC KH. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    destruct (fd_cell tl fast tb st1 TBL ltac:(lia) S1) as (NB1 & NB1f & NX1a & NX1b & SY1 & B10 & B11). specialize (NB1f FAST1).
    pose proof (fc_hi_lt tb st1 ltac:(lia) ltac:(lia)) as HI1.
    zstep. zstep. zstep.
    zstep. zchk.
    zstep. zstep.
    zstep. zchk.
    zstep. zchk.
    zshl. ldhi CELB DT tb st1.
    ldnx CELB DT tb st1.
    zstep.
    zstep. rnorm.
    zstep. rnorm. rewrite (hi_or (fc_hi tb st1) (fc_nx tb st1)) by lia.
    zstep. rnorm. rewrite (hi_nb tb st1) by lia.
    zstep.
    zstep. rewrite swrap32_small by lia.
    remember (fc_nb tb st1 + bc) as bc1 eqn:EBC1. assert (BC1 : 0 <= bc1 <= 109) by lia.
    zstep. rnorm. rewrite (hi_and (fc_hi tb st1) (fc_nx tb st1)) by lia.
    zstep.
    lazymatch goal with |- _ => let v := reg_val 25 in lazymatch v with Z_to_bv 64 ?e => set (b1 := e) end end.
    assert (B1R : 0 <= b1 < 2^(fc_nb tb st1)) by (apply fast_bits_lt; [apply Z.mod_pos_bound; lia | lia]). clearbody b1.
    zstep.
    zstep. set (st1a := b1 + fc_nx tb st1) in *. assert (S1a : 0 <= st1a < 2^tl) by (unfold st1a; lia). clearbody st1a.
    zstep.
    zstep.
    zstep. zchk.
    zstep.
    outst OUT OLEN.
    zstep. if_cases K; zify_cond K.
    - eapply fd2_finA with (st1 := st1a) (st2 := st2) (cont := cont) (bc := bc1) (pad := pad) (ptr := ptr); try eassumption; first [lia | close_fdcu].
    - eapply (fd2_t_rA _ _ _ st1a st2 bc1 j0 j ptr cont pad); [close_fdcu | exact S1a | exact S2 | lia | apply BOK; lia | exact HJ | exact HJC | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_t_loop : forall (f : nat) m1 out x1 st1 st2 bc j0 j ptr cont pad x24 x25 x26 x27,
    cap - j <= 2 * Z.of_nat f ->
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr -> bc <= 100 -> 0 <= j0 <= j -> j + 2 <= cap ->
    evt usegs POST (STT 0x2b9d8 m1 x1 st1 st2 bc j0 j ptr x24 x25 x26 x27 cont).
  Proof.
    induction f as [|f IH]; intros until x27; intros HF I S1 S2 BOK B100 HJ HJC; [exfalso; lia|].
    eapply fd2_t_head; [exact I | exact S1 | exact S2 | exact BOK | exact B100 | exact HJ | exact HJC |].
    unfold t2_KH. intros m2 out' st1' st2' bc' ptr' cont' y1 y24 y25 y26 y27 I2 S1' S2' BOK' B' J4.
    eapply (IH m2 out' y1 st1' st2' bc' j0 (j + 2) ptr' cont' pad); [lia | exact I2 | exact S1' | exact S2' | exact BOK' | exact B' | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd2_tprep : forall m1 out x1 st1 st2 bc j P cont pad x10 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    FDCm out st1 st2 cont bc pad P m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= j <= cap -> fbit_ok SRCI ni bc P -> bc <= 100 ->
    evt usegs POST (STE 0x2b94c m1 x1 st1 st2 bc j P cont x10 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 HJ BOK B100. open_fh HY. pose proof I as I0.
    zstep. zchk.
    zstep.
    zstep. zchk.
    zstep. zstep.
    zstep. if_cases K; zify_cond K.
    - zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      zb_goal. replace (Z_to_bv 64 0) with (Z_to_bv 64 (j - j)) by (f_equal; lia).
      eapply (fd2_t_loop (Z.to_nat cap) _ out _ st1 st2 bc j j P cont pad); [lia | exact I0 | exact S1 | exact S2 | exact BOK | exact B100 | lia | lia].
    - eapply fd2_t_err; exact I0.
  Qed.
End T2.
