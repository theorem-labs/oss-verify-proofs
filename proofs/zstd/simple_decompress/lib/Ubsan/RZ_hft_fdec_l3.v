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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_fse_decnf_kit RZ_fse_decf_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section L3.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis LOSU : lo <= SPV - 192.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Hypothesis FAST1 : fast = 1.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FDCm := (FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).

  (* [comment removed for export] *)
  Notation STL3 pc mm x1 st1 st2 bc j ptr x21 x22 x23 x24 x25 x26 x27 cont :=
    (STF pc mm x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j))
       (Z_to_bv 64 64) (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
       (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + cap + -3)) x21 x22 x23 x24 x25 x26 x27
       cont (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4))).
  Notation STE pc mm x1 st1 st2 bc j P cont x10 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j))
       x10 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
       (Z_to_bv 64 P) (Z_to_bv 64 (DST + cap)) x19 x20 x21 x22 x23 x24 x25 x26 x27 cont x29 x30 x31).

  Definition l3_KT (x1 : word) (pad : list byte) : Prop :=
    forall m2 out' st1' st2' bc' j' P cont' y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31,
      FDCm out' st1' st2' cont' bc' pad P m2 -> 0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= j' <= cap ->
      fbit_ok SRCI ni bc' P -> bc' <= 100 ->
      evt usegs POST (STE 0x2b94c m2 x1 st1' st2' bc' j' P cont' y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31).

  (* [comment removed for export] *)
  Lemma fd3_dec : forall m1 out x1 st1 st2 j bc cont pad ptr x21 x22 x23 x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> 0 <= j -> j + 4 <= cap ->
    (forall m2 out' bc' st1' st2' y21 y22 y23 y24 y25 y26, FDCm out' st1' st2' cont bc' pad ptr m2 ->
       0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= bc' <= 100 ->
       (bc' <= 64 -> evt usegs POST (STL3 0x2b680 m2 x1 st1' st2' bc' (j + 4) ptr y21 y22 y23 y24 y25 y26 x27 cont)) /\
       (64 < bc' -> evt usegs POST (STL3 0x2b920 m2 x1 st1' st2' bc' (j + 4) ptr y21 y22 y23 y24 y25 y26 x27 cont))) ->
    evt usegs POST (STL3 0x2b790 m1 x1 st1 st2 bc j ptr x21 x22 x23 x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I S1 S2 BCR HJ HJC KONT. open_fh HY. open_fdcu I.
    destruct TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    destruct (fd_cell tl fast tb st1 (conj TBLEN (conj TBBY TBOK)) ltac:(lia) S1) as (NB1 & NB1f & NX1a & NX1b & SY1 & B10 & B11). specialize (NB1f FAST1).
    pose proof (fc_hi_lt tb st1 ltac:(lia) ltac:(lia)) as HI1.
    zstep. zstep. zstep. zstep. zchk.
    zstep. zstep. zstep. zchk.
    zstep. zchk.
    zshl. ldhi CELB DT tb st1.
    ldnx CELB DT tb st1.
    zstep.
    zstep. rnorm.
    zstep. rnorm. rewrite (hi_or (fc_hi tb st1) (fc_nx tb st1)) by lia.
    zstep. rnorm. rewrite (hi_nb tb st1) by lia.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 5 in lazymatch v with Z_to_bv 64 ?e => set (b1 := e) end end.
    assert (B1R : 0 <= b1 < 2^(fc_nb tb st1)) by (apply fast_bits_lt; [apply Z.mod_pos_bound; lia | lia]). clearbody b1.
    zstep.
    zstep. rnorm. rewrite (hi_and (fc_hi tb st1) (fc_nx tb st1)) by lia.
    zstep. set (st1a := b1 + fc_nx tb st1) in *. assert (S1a : 0 <= st1a < 2^tl) by (unfold st1a; lia). clearbody st1a.
    zstep.
    zstep. zchk.
    destruct (fd_cell tl fast tb st2 (conj TBLEN (conj TBBY TBOK)) ltac:(lia) S2) as (NB2 & NB2f & NX2a & NX2b & SY2 & B20 & B21). specialize (NB2f FAST1).
    pose proof (fc_hi_lt tb st2 ltac:(lia) ltac:(lia)) as HI2.
    zstep. zstep. zstep. zstep. zstep.
    outst OUT OLEN.
    zstep. zchk.
    zstep. zstep. zstep. zchk.
    zstep. zchk.
    zshl. ldnx CELB DT tb st2.
    ldhi CELB DT tb st2.
    zstep. zstep. zstep.
    zstep. rnorm.
    zstep. rnorm. rewrite (hi_or (fc_hi tb st2) (fc_nx tb st2)) by lia.
    zstep. rewrite (hi_nbw tb st2 (fc_nx tb st2)) by lia.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 24 in lazymatch v with Z_to_bv 64 ?e => set (b2 := e) end end.
    assert (B2R : 0 <= b2 < 2^(fc_nb tb st2)) by (apply fast_bits_lt; [apply Z.mod_pos_bound; lia | lia]). clearbody b2.
    zstep. zstep. zstep. zmod_small.
    zstep.
    zstep. rnorm. rewrite (hi_and (fc_hi tb st2) (fc_nx tb st2)) by lia.
    zstep. set (st2a := b2 + fc_nx tb st2) in *. assert (S2a : 0 <= st2a < 2^tl) by (unfold st2a; lia). clearbody st2a.
    zstep.
    outst OUT OLEN.
    destruct (fd_cell tl fast tb st1a (conj TBLEN (conj TBBY TBOK)) ltac:(lia) S1a) as (NB3 & NB3f & NX3a & NX3b & SY3 & B30 & B31). specialize (NB3f FAST1).
    pose proof (fc_hi_lt tb st1a ltac:(lia) ltac:(lia)) as HI3.
    zstep. zchk.
    zstep. zstep. zstep. zchk.
    zstep. zchk.
    zshl. ldhi CELB DT tb st1a.
    ldnx CELB DT tb st1a.
    zstep.
    zstep. rnorm.
    zstep. rnorm. rewrite (hi_or (fc_hi tb st1a) (fc_nx tb st1a)) by lia.
    zstep. rnorm. rewrite (hi_nb tb st1a) by lia.
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 5 in lazymatch v with Z_to_bv 64 ?e => set (b3 := e) end end.
    assert (B3R : 0 <= b3 < 2^(fc_nb tb st1a)) by (apply fast_bits_lt; [apply Z.mod_pos_bound; lia | lia]). clearbody b3.
    zstep.
    zstep. rnorm. rewrite (hi_and (fc_hi tb st1a) (fc_nx tb st1a)) by lia.
    zstep. set (st1b := b3 + fc_nx tb st1a) in *. assert (S1b : 0 <= st1b < 2^tl) by (unfold st1b; lia). clearbody st1b.
    zstep.
    zstep. zchk.
    zstep. zstep. zstep. zstep.
    outst OUT OLEN.
    destruct (fd_cell tl fast tb st2a (conj TBLEN (conj TBBY TBOK)) ltac:(lia) S2a) as (NB4 & NB4f & NX4a & NX4b & SY4 & B40 & B41). specialize (NB4f FAST1).
    pose proof (fc_hi_lt tb st2a ltac:(lia) ltac:(lia)) as HI4.
    zstep. zchk.
    zstep. zstep. zstep. zchk.
    zstep. zchk.
    zshl. ldhi CELB DT tb st2a.
    ldnx CELB DT tb st2a.
    zstep.
    zstep. rnorm.
    zstep. rnorm. rewrite (hi_or (fc_hi tb st2a) (fc_nx tb st2a)) by lia.
    zstep. rnorm. rewrite (hi_nb tb st2a) by lia.
    zstep.
    zstep. rewrite (swrap32_small (fc_nb tb st2a + (fc_nb tb st1a + (fc_nb tb st2 + (fc_nb tb st1 + bc))))) by lia.
    zstep.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => set (b4 := e) end end.
    assert (B4R : 0 <= b4 < 2^(fc_nb tb st2a)) by (apply fast_bits_lt; [apply Z.mod_pos_bound; lia | lia]). clearbody b4.
    zstep.
    zstep. rnorm. rewrite (hi_and (fc_hi tb st2a) (fc_nx tb st2a)) by lia.
    zstep. set (st2b := b4 + fc_nx tb st2a) in *. assert (S2b : 0 <= st2b < 2^tl) by (unfold st2b; lia). clearbody st2b.
    zstep.
    zstep. zchk.
    zstep.
    outst OUT OLEN.
    zstep. zchk.
    zstep. replace (DST + j + 4) with (DST + (j + 4)) by lia.
    set (bc4 := fc_nb tb st2a + (fc_nb tb st1a + (fc_nb tb st2 + (fc_nb tb st1 + bc)))) in *.
    assert (BC4 : 0 <= bc4 <= 100) by (unfold bc4; lia). clearbody bc4.
    zstep. if_cases K16; zify_cond K16.
    - eapply (proj1 (KONT _ _ bc4 st1b st2b _ _ _ _ _ _ ltac:(close_fdcu) S1b S2b BC4)). lia.
    - eapply (proj2 (KONT _ _ bc4 st1b st2b _ _ _ _ _ _ ltac:(close_fdcu) S1b S2b BC4)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fd3_load : forall m1 out x1 st1 st2 bc j ptr flag cont pad x22 x23 x24 x25 x26 x27 x28,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    SRCI <= ptr -> ptr + 8 <= SRCI + ni -> 0 <= flag <= 1 -> 0 <= j <= cap ->
    (forall m2 cont' y22 y23 y24 y25 y26, FDCm out st1 st2 cont' bc pad ptr m2 -> flag = 1 -> j + 4 <= cap ->
       evt usegs POST (STL3 0x2b790 m2 x1 st1 st2 bc j ptr (Z_to_bv 64 flag) y22 y23 y24 y25 y26 x27 cont')) ->
    (forall m2 cont' y22 y23 y24 y25 y26, FDCm out st1 st2 cont' bc pad ptr m2 ->
       evt usegs POST (STE 0x2b94c m2 x1 st1 st2 bc j ptr cont' (Z_to_bv 64 64) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + cap + -3)) (Z_to_bv 64 flag)
                           y22 y23 y24 y25 y26 x27 (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4)))) ->
    evt usegs POST (STL3 0x2b72c m1 x1 st1 st2 bc j ptr (Z_to_bv 64 flag) x22 x23 x24 x25 x26 x27 x28).
  Proof.
    intros until x28; intros I PLO PHI FLR HJ KD KT. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB. do 9 zstep.
    zstep.
    zstep. if_cases K; zify_cond K.
    - eapply KT. close_fdcu.
    - zstep. if_cases K2; zify_cond K2.
      + eapply KT. close_fdcu.
      + eapply KD; [close_fdcu | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd3_head : forall m1 out x1 st1 st2 bc j ptr cont pad x21 x22 x23 x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j <= cap ->
    (forall m2 bc' ptr' cont' y21 y22 y23 y24 y25 y26, FDCm out st1 st2 cont' bc' pad ptr' m2 -> 0 <= bc' <= 64 ->
       8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8 -> j + 4 <= cap ->
       evt usegs POST (STL3 0x2b790 m2 x1 st1 st2 bc' j ptr' y21 y22 y23 y24 y25 y26 x27 cont')) ->
    (forall m2 bc' ptr' cont' y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31, FDCm out st1 st2 cont' bc' pad ptr' m2 -> 0 <= bc' <= 64 ->
       (ptr' = SRCI \/ (8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8)) ->
       evt usegs POST (STE 0x2b94c m2 x1 st1 st2 bc' j ptr' cont' y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31)) ->
    evt usegs POST (STL3 0x2b680 m1 x1 st1 st2 bc j ptr x21 x22 x23 x24 x25 x26 x27 cont).
  Proof.
    intros until x27; intros I BCR PV HJ KD KT. open_fh HY. pose proof I as I0. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
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
      zstep. zstep.
      zstep. zchk.
      zstep. zstep.
      eapply (fd3_load _ out x1 st1 st2 _ j _ 1 cont pad); [close_fdcu | lia | lia | lia | lia | |].
      + intros mq cont' y22 y23 y24 y25 y26 I2 _ J4. eapply KD; [exact I2 | lia | lia | exact J4].
      + intros mq cont' y22 y23 y24 y25 y26 I2. eapply KT; [exact I2 | lia | right; lia].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply KT; [exact I0 | exact BCR | left; lia].
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
          zstep. zstep.
          zstep. zchk.
          zstep. zstep. zflag 1.
          zstep. zstep.
          eapply (fd3_load _ out x1 st1 st2 _ j _ 1 cont pad); [close_fdcu | lia | lia | lia | lia | |].
          -- intros mq cont' y22 y23 y24 y25 y26 I2 _ J4. eapply KD; [exact I2 | lia | lia | exact J4].
          -- intros mq cont' y22 y23 y24 y25 y26 I2. eapply KT; [exact I2 | lia | right; lia].
        * (* [comment removed for export] *)
          zstep. rnorm.
          zstep. zstep. rnorm.
          zstep. zchk.
          zstep. zstep. zstep.
          zstep. zchk.
          zstep. rnorm.
          zstep. rnorm.
          zstep. rewrite swrap32_small by lia.
          zstep. zstep.
          zstep. zchk.
          zstep. zstep. zflag 0.
          zstep. zstep.
          eapply (fd3_load _ out x1 st1 st2 _ j _ 0 cont pad); [close_fdcu | lia | lia | lia | lia | |].
          -- intros. exfalso; lia.
          -- intros mq cont' y22 y23 y24 y25 y26 I2. eapply KT; [exact I2 | lia | left; lia].
  Qed.

  Lemma fd3_ovf : forall m1 out x1 st1 st2 bc j ptr cont pad x10 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    l3_KT x1 pad ->
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 64 < bc <= 100 -> 0 <= j <= cap ->
    evt usegs POST
      (STF 0x2b940 m1 x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + j))
         x10 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
         x17 (Z_to_bv 64 (DST + cap)) x19 x20 x21 x22 x23 x24 x25 x26 x27 cont x29 x30 x31).
  Proof.
    intros until x31; intros KT I S1 S2 BCR HJ. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. zstep. zstep.
    eapply KT; [close_fdcu | exact S1 | exact S2 | exact HJ | unfold fbit_ok; split; [lia | intros; lia] | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd3_loop : forall (f : nat) m1 out x1 st1 st2 bc j ptr cont pad x21 x22 x23 x24 x25 x26 x27,
    cap - j <= 4 * Z.of_nat f -> l3_KT x1 pad ->
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j <= cap ->
    evt usegs POST (STL3 0x2b680 m1 x1 st1 st2 bc j ptr x21 x22 x23 x24 x25 x26 x27 cont).
  Proof.
    induction f as [|f IH]; intros until x27; intros HF KT I S1 S2 BCR PV HJ.
    - eapply fd3_head; [exact I | exact BCR | exact PV | exact HJ | intros; exfalso; lia |].
      intros m2 bc' ptr' cont' y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 I2 B' P'.
      eapply KT; [exact I2 | exact S1 | exact S2 | exact HJ | unfold fbit_ok; split; [lia | intros _; exact P'] | lia].
    - eapply fd3_head; [exact I | exact BCR | exact PV | exact HJ | |].
      + intros m2 bc' ptr' cont' y21 y22 y23 y24 y25 y26 I2 B' P' J4.
        eapply fd3_dec; [exact I2 | exact S1 | exact S2 | exact B' | lia | exact J4 |].
        intros m3 out' bc2 st1' st2' z21 z22 z23 z24 z25 z26 I3 S1' S2' B2. split.
        * intros LE. eapply (IH m3 out' x1 st1' st2' bc2 (j + 4) ptr' cont' pad); [lia | exact KT | exact I3 | exact S1' | exact S2' | lia | right; exact P' | lia].
        * intros GT. zstep.
          eapply (fd3_ovf m3 out' x1 st1' st2' bc2 (j + 4) ptr' cont' pad); [exact KT | exact I3 | exact S1' | exact S2' | lia | lia].
      + intros m2 bc' ptr' cont' y10 y19 y20 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 I2 B' P'.
        eapply KT; [exact I2 | exact S1 | exact S2 | exact HJ | unfold fbit_ok; split; [lia | intros _; exact P'] | lia].
  Qed.

  Lemma fd3_loop0u : forall m1 out x1 st1 st2 bc ptr cont pad x21 x22 x23 x24 x25 x26 x27,
    l3_KT x1 pad ->
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) ->
    evt usegs POST
      (STF 0x2b680 m1 x1 (Z_to_bv 64 st1) (Z_to_bv 64 st2) (Z_to_bv 64 bc) (Z_to_bv 64 DST) (Z_to_bv 64 DST)
         (Z_to_bv 64 64) (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 SRCI) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 65535)
         (Z_to_bv 64 ptr) (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (-5)) (Z_to_bv 64 (DST + cap + -3)) x21 x22 x23 x24 x25 x26 x27
         cont (Z_to_bv 64 1) (Z_to_bv 64 (-3)) (Z_to_bv 64 (-4))).
  Proof.
    intros until x27; intros KT I S1 S2 BCR PV.
    pose proof (fd3_loop (Z.to_nat cap) m1 out x1 st1 st2 bc 0 ptr cont pad x21 x22 x23 x24 x25 x26 x27) as L.
    replace (DST + 0) with DST in L by lia.
    open_fh HY. apply L; try assumption; lia.
  Qed.
End L3.
