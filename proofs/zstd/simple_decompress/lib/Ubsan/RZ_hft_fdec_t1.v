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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_fse_decnf_kit fse_kit_dsym RZ_hft_fdec_epi.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section T1.
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
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FDCm := (FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).
  Notation STT0 pc mm x1 x5 x6 x7 x10 x15 x16 x17 j x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) x10 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1)
         x15 x16 x17 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 (DST + j)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Notation PV p := (p = SRCI \/ (8 <= ni /\ SRCI <= p <= SRCI + ni - 8)).

  Ltac ldnb CELB DT tb st :=
    let a := cur_mem_addr in
    let RDc := fresh "RDc" in
    pose proof (u8ro_znth usegs _ (DT + 4) tb (4 * st + 3) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
    zstep; cbv beta; fold (fc_nb tb st); rewrite (byte_lit (fc_nb tb st)) by lia; clear RDc.
  Ltac ldsy CELB DT tb st :=
    let a := cur_mem_addr in
    let RDc := fresh "RDc" in
    pose proof (u8ro_znth usegs _ (DT + 4) tb (4 * st + 2) a CELB ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
    zstep; cbv beta; fold (fc_sy tb st); rewrite (byte_lit (fc_sy tb st)) by lia; clear RDc.
  Ltac ldnx CELB DT tb st :=
    let a := cur_mem_addr in
    let RDc := fresh "RDc" in
    pose proof (fc_nx_rd _ (DT + 4) tb st a CELB ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RDc;
    zstep; rewrite (zx16_u (fc_nx tb st)) by lia; clear RDc.
  Ltac ldmask MI nb :=
    let a := cur_mem_addr in
    let RDc := fresh "RDc" in
    pose proof (fbitmask_rd _ nb a MI ltac:(lia) ltac:(unfold wa, FBITMASK; f_equal; lia)) as RDc;
    zstep; clear RDc.
  Ltac ldm MI nb :=
    ldmask MI nb;
    let M := fresh "M" in
    assert (M : 1 <= 2^nb <= 2^tl) by (split; [pose proof (Z.pow_pos_nonneg 2 nb ltac:(lia) ltac:(lia)); lia | apply Z.pow_le_mono_r; lia]);
    rewrite (zx32w_small (2^nb - 1)) by lia; znorm.
  Ltac setr r b := let v := reg_val r in lazymatch v with Z_to_bv 64 ?e => set (b := e) in * end.
  Ltac setbits r b nb :=
    setr r b; let B := fresh "B" in assert (B : 0 <= b < 2^nb) by (apply fland_mask_lt; lia); clearbody b.
  Ltac setst r st :=
    setr r st; let S := fresh "S" in assert (S : 0 <= st < 2^tl) by (unfold st; lia); clearbody st.
  Ltac srl3 bc := zstep; rewrite (srliw_val bc 3) by lia; rewrite (Z.mod_small bc 4294967296) by lia; change (2^3) with 8.
  Ltac secs := first [exact HY | exact LOSU | exact SPA | exact TBL | exact SRCLEN | exact OFFWK | exact WKR0 | exact DSYM | exact DSYMF].

  (* [comment removed for export] *)
  Notation STH pc mm x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 (Z_to_bv 64 64) (Z_to_bv 64 (-1)) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952)
         (Z_to_bv 64 (-70)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 (DST + cap + -2))
         (Z_to_bv 64 18446744073709481391) (Z_to_bv 64 2) (Z_to_bv 64 (DST + j + 1)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK)
         (Z_to_bv 64 (DST + j0)) (Z_to_bv 64 (j0 - j)) x23 x24 x25 x26 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma fd1_t_err : forall m1 out st1 st2 cont bc pad ptr x1 x5 x6 x7 x8 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    evt usegs POST (STF 0x2b964 m1 x1 x5 x6 x7 x8 x9 (Z_to_bv 64 (-70)) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I.
    replace (Z_to_bv 64 (-70)) with (Z_to_bv 64 18446744073709551546) by (apply bv_eq; reflexivity).
    eapply fd_epi; try secs.
    all: first [eapply fdcu_fdu; exact I | lia | (left; reflexivity)].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_j2 : forall m1 out x1 st1 st2 cont bc pad ptr j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= j -> j + 2 <= cap ->
    (forall y28, j + 4 <= cap -> evt usegs POST (STH 0x2b330 m1 x1 j0 (j + 2) x23 x24 x25 x26 x27 y28 x29 x30 x31)) ->
    evt usegs POST (STH 0x2b31c m1 x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HJ HJC KH. open_fh HY.
    zn. zn. zn. zn.
    try replace (Z_to_bv 64 (j0 - j + -2)) with (Z_to_bv 64 (j0 - (j + 2))) by (f_equal; lia).
    try replace (Z_to_bv 64 (DST + j + 3)) with (Z_to_bv 64 (DST + (j + 2) + 1)) by (f_equal; lia).
    try replace (Z_to_bv 64 (DST + j + 2)) with (Z_to_bv 64 (DST + (j + 2))) by (f_equal; lia).
    zstep. if_cases K; zify_cond K.
    - eapply fd1_t_err; exact I.
    - eapply KH. lia.
  Qed.

  (* [comment removed for export] *)
  Definition t1_KH (x1 : word) (j0 j : Z) (x26 x27 : word) : Prop :=
    forall m2 out' st1' st2' cont' bc' pad' ptr' y23 y24 y25 y28 y29 y30 y31, FDCm out' st1' st2' cont' bc' pad' ptr' m2 ->
      0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= bc' <= 64 -> PV ptr' -> j + 4 <= cap ->
      evt usegs POST (STH 0x2b330 m2 x1 j0 (j + 2) y23 y24 y25 x26 x27 y28 y29 y30 y31).

  (* [comment removed for export] *)
  Lemma fd1_t_rB_load : forall m1 out x1 st1 st2 cont bc pad ptr j0 j bcn ptrn x23 x24 x25 x26 x27 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= bcn <= 64 -> 8 <= ni -> SRCI <= ptrn -> ptrn + 8 <= SRCI + ni -> 4096 <= ptr < 2^47 ->
    (forall m2 cont' bc' pad' ptr' y23 y24 y25 y28 y29 y30 y31, FDCm out st1 st2 cont' bc' pad' ptr' m2 -> 0 <= bc' <= 64 -> PV ptr' ->
       evt usegs POST (STH 0x2b31c m2 x1 j0 j y23 y24 y25 x26 x27 y28 y29 y30 y31)) ->
    evt usegs POST (STH 0x2b5cc m1 x1 j0 j x23 x24 x25 x26 x27 (Z_to_bv 64 ptrn) (Z_to_bv 64 bcn) (Z_to_bv 64 ptr) x31).
  Proof.
    intros until x31; intros I BCR NI8 PLO PHI PNZ KJ. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zn. zn. zc.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
    do 11 zstep.
    eapply KJ; [close_fdcu | lia | right; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_rB : forall m1 out x1 st1 st2 cont bc pad ptr j0 j x23 x24 x25 x26 x27 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= bc <= 64 -> PV ptr ->
    (forall m2 cont' bc' pad' ptr' y23 y24 y25 y28 y29 y30 y31, FDCm out st1 st2 cont' bc' pad' ptr' m2 -> 0 <= bc' <= 64 -> PV ptr' ->
       evt usegs POST (STH 0x2b31c m2 x1 j0 j y23 y24 y25 x26 x27 y28 y29 y30 y31)) ->
    evt usegs POST (STH 0x2b544 m1 x1 j0 j x23 x24 x25 x26 x27 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 bc) x30 x31).
  Proof.
    intros until x31; intros I BCR PV0 KJ. open_fh HY. pose proof I as I0. open_fdcu I0.
    assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc /\ bc mod 8 = bc - 8 * (bc / 8)) by (clear - BCR; Z.div_mod_to_equations; lia).
    zn. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      srl3 bc. zc. zn. zn. zn. zn. zc. zn. zn.
      eapply fd1_t_rB_load; [exact I | lia | lia | lia | lia | lia | exact KJ].
    - zn. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply KJ; [exact I | lia | exact PV0].
      + (* [comment removed for export] *)
        srl3 bc. zc. zn. zn. zn. zn. zc. zn.
        zstep. if_cases K3; zify_cond K3.
        * zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn.
          eapply fd1_t_rB_load; [exact I | lia | lia | lia | lia | lia | exact KJ].
        * zn. zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn.
          eapply fd1_t_rB_load; [exact I | lia | lia | lia | lia | lia | exact KJ].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_mid : forall m1 out x1 st1 st2 cont bc pad ptr j0 j x23 x24 x25 x26 x27 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> PV ptr -> 0 <= j -> j + 2 <= cap ->
    t1_KH x1 j0 j x26 x27 ->
    evt usegs POST (STH 0x2b4b4 m1 x1 j0 j x23 x24 x25 x26 x27 (Z_to_bv 64 (SRCI + 8)) x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV0 HJ HJC KH. open_fh HY. pose proof I as I0. open_fdcu I0.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    destruct (fd_cell tl fast tb st2 TBL ltac:(lia) S2) as (NB2 & _ & NX2a & NX2b & SY2 & B20 & B21).
    assert (SX : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z)
      by (intros z Hz; unfold sx32; f_equal; rewrite unsigned_lit by lia; apply swrap32_small; lia).
    zstep. if_cases K0; zify_cond K0.
    - eapply fd1_t_err; exact I.
    - zn. zn. zn. zn. zc. zn. zn. zc. zc. zn.
      ldhi CELB DT tb st2. znorm. zn. zn. zc. zn. zn. zc.
      ldnx CELB DT tb st2. znorm. zn. zn. rewrite (SX bc) by lia. znorm. zn. zn.
      ldm MI (fc_nb tb st2). zn.
      setr 29 bc2. assert (BC2 : bc <= bc2 <= bc + fc_nb tb st2) by (unfold bc2; lia). clearbody bc2.
      zn. zn. zn. zn. setbits 31 b2 (fc_nb tb st2).
      zn. zn. setst 31 st2a.
      zn. zc. zn. outst OUT OLEN. znorm.
      zstep. if_cases KB; zify_cond KB.
      + eapply fd1_finB; try secs.
        all: first [close_fdcu | exact S1 | lia].
      + eapply fd1_t_rB; [close_fdcu | lia | exact PV0 |].
        intros m2 cont' bc' pad' ptr' y23 y24 y25 y28 y29 y30 y31 I2 BC' PV'.
        eapply fd1_t_j2; [exact I2 | lia | lia |].
        intros y28' J4. eapply KH; [exact I2 | exact S1 | exact S | lia | exact PV' | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_rA_load : forall m1 out x1 st1 st2 cont bc pad ptr j0 j bcn ptrn x23 x24 x25 x26 x27,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= bcn <= 64 -> 8 <= ni -> SRCI <= ptrn -> ptrn + 8 <= SRCI + ni -> 4096 <= ptr < 2^47 ->
    (forall m2 cont' bc' pad' ptr' y23 y24 y25 y29 y30 y31, FDCm out st1 st2 cont' bc' pad' ptr' m2 -> 0 <= bc' <= 64 -> PV ptr' ->
       evt usegs POST (STH 0x2b4b4 m2 x1 j0 j y23 y24 y25 x26 x27 (Z_to_bv 64 (SRCI + 8)) y29 y30 y31)) ->
    evt usegs POST (STH 0x2b44c m1 x1 j0 j x23 x24 x25 x26 x27 (Z_to_bv 64 (SRCI + 8)) (Z_to_bv 64 bcn) (Z_to_bv 64 ptr) (Z_to_bv 64 ptrn)).
  Proof.
    intros until x27; intros I BCR NI8 PLO PHI PNZ KM. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zn. zn. zc.
    lbyte SRCB. lbyte SRCB. lbyte SRCB. lbyte SRCB. do 4 zstep. lbyte SRCB. lbyte SRCB. zstep. lbyte SRCB. lbyte SRCB.
    do 10 zstep.
    eapply KM; [close_fdcu | lia | right; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_rA : forall m1 out x1 st1 st2 cont bc pad ptr j0 j x23 x24 x25 x26 x27 x28 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= bc <= 64 -> PV ptr ->
    (forall m2 cont' bc' pad' ptr' y23 y24 y25 y29 y30 y31, FDCm out st1 st2 cont' bc' pad' ptr' m2 -> 0 <= bc' <= 64 -> PV ptr' ->
       evt usegs POST (STH 0x2b4b4 m2 x1 j0 j y23 y24 y25 x26 x27 (Z_to_bv 64 (SRCI + 8)) y29 y30 y31)) ->
    evt usegs POST (STH 0x2b3c0 m1 x1 j0 j x23 x24 x25 x26 x27 x28 (Z_to_bv 64 bc) x30 x31).
  Proof.
    intros until x31; intros I BCR PV0 KM. open_fh HY. pose proof I as I0. open_fdcu I0.
    assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc /\ bc mod 8 = bc - 8 * (bc / 8)) by (clear - BCR; Z.div_mod_to_equations; lia).
    zn. zn. zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      srl3 bc. zc. zn. zn. zn. zn. zc. zn. zn.
      eapply fd1_t_rA_load; [exact I | lia | lia | lia | lia | lia | exact KM].
    - zn. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        eapply KM; [exact I | lia | exact PV0].
      + (* [comment removed for export] *)
        srl3 bc. zc. zn. zn. zn. zn. zc. zn.
        zstep. if_cases K3; zify_cond K3.
        * zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn.
          eapply fd1_t_rA_load; [exact I | lia | lia | lia | lia | lia | exact KM].
        * zn. zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn.
          eapply fd1_t_rA_load; [exact I | lia | lia | lia | lia | lia | exact KM].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_head : forall m1 out x1 st1 st2 cont bc pad ptr j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr -> bc <= 100 -> 0 <= j -> j + 2 <= cap ->
    t1_KH x1 j0 j x26 x27 ->
    evt usegs POST (STH 0x2b330 m1 x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I S1 S2 (BCR & BOK) B100 HJ HJC KH. open_fh HY. pose proof I as I0. open_fdcu I0.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    destruct (fd_cell tl fast tb st1 TBL ltac:(lia) S1) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    assert (SX : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z)
      by (intros z Hz; unfold sx32; f_equal; rewrite unsigned_lit by lia; apply swrap32_small; lia).
    zn. zn. zn. zn. zc. zn. zn. zc. zc. zn.
    ldhi CELB DT tb st1. znorm. zn. zn. zc. zn. zn. zc.
    ldnx CELB DT tb st1. znorm. zn. zn. rewrite (SX bc) by lia. znorm. zn. zn.
    ldm MI (fc_nb tb st1). zn.
    setr 29 bc1. assert (BC1 : bc <= bc1 <= bc + fc_nb tb st1) by (unfold bc1; lia). clearbody bc1.
    zn. zn. zn. zn. zn. setbits 30 b1 (fc_nb tb st1).
    zn. setst 30 st1a.
    zn. zn. zc. zn. outst OUT OLEN. znorm.
    zstep. if_cases KB; zify_cond KB.
    - eapply fd1_finA; try secs.
      all: first [close_fdcu | exact S2 | lia].
    - eapply fd1_t_rA; [close_fdcu | lia | apply BOK; lia |].
      intros m2 cont' bc' pad' ptr' y23 y24 y25 y29 y30 y31 I2 BC' PV'.
      eapply fd1_t_mid; [exact I2 | exact S | exact S2 | lia | exact PV' | lia | lia | exact KH].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_t_loop : forall (f : nat) m1 out x1 st1 st2 cont bc pad ptr j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31,
    cap - j <= 2 * Z.of_nat f ->
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> fbit_ok SRCI ni bc ptr -> bc <= 100 -> 0 <= j -> j + 2 <= cap ->
    evt usegs POST (STH 0x2b330 m1 x1 j0 j x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros HF I S1 S2 BOK B100 HJ HJC; [exfalso; lia|].
    eapply fd1_t_head; [exact I | exact S1 | exact S2 | exact BOK | exact B100 | exact HJ | exact HJC |].
    unfold t1_KH. intros m2 out' st1' st2' cont' bc' pad' ptr' y23 y24 y25 y28 y29 y30 y31 I2 S1' S2' BB PB J4.
    eapply (IH m2 out' x1 st1' st2'); [lia | exact I2 | exact S1' | exact S2' | unfold fbit_ok; split; [lia | intros _; exact PB] | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_tprep : forall m2 out' bc' st2' st1' cont' pad' ptr' j' y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
    FDCm out' st1' st2' cont' bc' pad' ptr' m2 -> 0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= j' <= cap -> fbit_ok SRCI ni bc' ptr' -> bc' <= 100 ->
    evt usegs POST (STT0 0x2b2e4 m2 y1 y5 y6 y7 y10 y15 y16 y17 j' y22 y23 y24 y25 y26 y27 y28 y29 y30 y31).
  Proof.
    intros until y31; intros I S1 S2 HJ BOK B100. open_fh HY.
    zc. zn. zc. zn. zn.
    zstep. if_cases KE; zify_cond KE.
    - eapply fd1_t_err; exact I.
    - do 8 zn.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (j' - j')) by (f_equal; lia).
      eapply (fd1_t_loop (Z.to_nat cap)); [lia | exact I | exact S1 | exact S2 | exact BOK | exact B100 | lia | lia].
  Qed.
End T1.
