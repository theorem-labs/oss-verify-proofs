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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_kit RZ_hft_fdec_defs RZ_fse_decnf_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section L1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV lo DST cap WK wksz SRCI ni DT tl fast : Z) (srci : list byte) (tb : list Z).
  Hypothesis HY : fd_hyps SPV lo DST cap SRCI ni DT tl.
  Hypothesis LOSU : lo <= SPV - 192.
  Hypothesis SPA : SPV mod 16 = 0.
  Hypothesis TBL : fd_tbl tl fast tb.
  Hypothesis SRCLEN : Z.of_nat (length srci) = ni.
  Notation POST := (fse_dec_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DST cap WK wksz lo m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -192)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation FDCm := (FDCU s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra m SPV lo DST cap WK wksz SRCI DT srci tb).

  (* [comment removed for export] *)
  Notation STL1 pc mm x1 bc st2 st1 ptr j x23 x24 x25 x26 x27 x31 :=
    (STF pc mm x1 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8))
         (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SRCI) (Z_to_bv 64 ptr) (Z_to_bv 64 (-3))
         (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + cap + -3)) x23
         x24 x25 x26 x27 (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 st1) x31).
  Notation STLD pc mm x1 bc st2 st1 ptr j x24 x25 x26 x27 x28 x31 :=
    (STF pc mm x1 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8))
         (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SRCI) (Z_to_bv 64 ptr) (Z_to_bv 64 (-3))
         (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 (DST + j)) (Z_to_bv 64 (DST + cap + -3)) (Z_to_bv 64 bc)
         x24 x25 x26 x27 x28 (Z_to_bv 64 st2) (Z_to_bv 64 st1) x31).
  Notation STT0 pc mm x1 x5 x6 x7 x10 x15 x16 x17 j x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) x10 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1)
         x15 x16 x17 (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 (DST + j)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Notation KEXIT :=
    (forall m2 out' bc' st2' st1' cont' pad' ptr' j' y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
       FDCm out' st1' st2' cont' bc' pad' ptr' m2 -> 0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= j' <= cap -> fbit_ok SRCI ni bc' ptr' -> bc' <= 100 ->
       evt usegs POST (STT0 0x2b2e4 m2 y1 y5 y6 y7 y10 y15 y16 y17 j' y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)).

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

  (* [comment removed for export] *)
  Lemma fd1_dec : forall m1 out x1 bc st2 st1 cont pad ptr j x24 x25 x26 x27 x28 c6,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    0 <= st1 < 2^tl -> 0 <= st2 < 2^tl -> 0 <= bc <= 64 -> 0 <= j -> j + 4 <= cap ->
    (forall m2 out' bc' st2' st1' y1 y23 y24 y25 y26 y27 y31, FDCm out' st1' st2' cont bc' pad ptr m2 ->
       0 <= st1' < 2^tl -> 0 <= st2' < 2^tl -> 0 <= bc' <= 100 ->
       (bc' <= 64 -> evt usegs POST (STL1 0x2afdc m2 y1 bc' st2' st1' ptr (j + 4) y23 y24 y25 y26 y27 y31)) /\
       (64 < bc' -> evt usegs POST (STL1 0x2b2d8 m2 y1 bc' st2' st1' ptr (j + 4) y23 y24 y25 y26 y27 y31))) ->
    evt usegs POST (STLD 0x2b0ec m1 x1 bc st2 st1 ptr j x24 x25 x26 x27 x28 c6).
  Proof.
    intros until c6; intros I S1 S2 BCR HJ HJC KONT. open_fh HY. open_fdcu I.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    destruct (fd_cell tl fast tb st1 TBL ltac:(lia) S1) as (NB1 & _ & NX1a & NX1b & SY1 & B10 & B11).
    destruct (fd_cell tl fast tb st2 TBL ltac:(lia) S2) as (NB2 & _ & NX2a & NX2b & SY2 & B20 & B21).
    zn. zn. zn. zc. zn. zn. zc. zc. zn.
    ldhi CELB DT tb st1. znorm. zn. zn. zc. zn. zn. zn. zc.
    ldnx CELB DT tb st1. znorm. zn. zn. zn.
    ldm MI (fc_nb tb st1). zn. zn. zn. zn. setbits 30 b1 (fc_nb tb st1).
    zn. zn. setst 30 st1a.
    destruct (fd_cell tl fast tb st1a TBL ltac:(lia) S) as (NB3 & _ & NX3a & NX3b & SY3 & B30 & B31).
    zn. zc. zn.
    zn. zn. zn. outst OUT OLEN. znorm. zc. zn. zn. zc. zc. zn.
    ldhi CELB DT tb st2. znorm. zn. zn. zc. zn. zn. zc.
    ldnx CELB DT tb st2. znorm. zn. zn. zn. zn.
    ldm MI (fc_nb tb st2). zn. zn. zn. zn. zn. setbits 25 b2 (fc_nb tb st2).
    zn. zn. zn. setst 29 st2a.
    destruct (fd_cell tl fast tb st2a TBL ltac:(lia) S0) as (NB4 & _ & NX4a & NX4b & SY4 & B40 & B41).
    zn. outst OUT OLEN. znorm. zc.
    zn. zn. zc. zn.
    ldhi CELB DT tb st1a. znorm. zn. zn. zc. zn. zn. zc.
    ldnx CELB DT tb st1a. znorm. zn. zn. zn.
    ldm MI (fc_nb tb st1a). zn. zn. zn. zn. setbits 30 b3 (fc_nb tb st1a).
    zn. zn. setst 30 st1b.
    zn. zc. zn. zn. zn. outst OUT OLEN. znorm. zc. zn. zn. zc. zn.
    ldhi CELB DT tb st2a. znorm. zn. zn. zc. zn. zn. zc.
    ldnx CELB DT tb st2a. znorm. zn. zn.
    setr 28 bc4. assert (BC4 : 0 <= bc4 <= 100) by (unfold bc4; lia). clearbody bc4.
    zn. ldm MI (fc_nb tb st2a). zn. zn. zn. zn. setbits 29 b4 (fc_nb tb st2a).
    zn. zn. setst 29 st2b.
    zn. zc. zn. outst OUT OLEN. znorm. zc. zn.
    zstep. replace (DST + j + 4) with (DST + (j + 4)) by lia. if_cases KB; zify_cond KB.
    - eapply (proj1 (KONT _ _ bc4 st2b st1b _ _ _ _ _ _ _ ltac:(close_fdcu) ltac:(lia) ltac:(lia) BC4)). lia.
    - eapply (proj2 (KONT _ _ bc4 st2b st1b _ _ _ _ _ _ _ ltac:(close_fdcu) ltac:(lia) ltac:(lia) BC4)). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_load : forall m1 out x1 bc st2 st1 cont pad ptr j flag x24 x25 x26 x27 x31,
    FDCm out st1 st2 cont bc pad ptr m1 ->
    SRCI <= ptr -> ptr + 8 <= SRCI + ni -> 0 <= flag <= 1 -> 0 <= j <= cap ->
    (forall m2 cont' y1 y24 y25 y26 y27 y28 y31, FDCm out st1 st2 cont' bc pad ptr m2 -> flag = 1 -> j + 4 <= cap ->
       evt usegs POST (STLD 0x2b0ec m2 y1 bc st2 st1 ptr j y24 y25 y26 y27 y28 y31)) ->
    (forall m2 cont' y1 y5 y6 y7 y10 y15 y16 y17 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31, FDCm out st1 st2 cont' bc pad ptr m2 ->
       evt usegs POST (STT0 0x2b2e4 m2 y1 y5 y6 y7 y10 y15 y16 y17 j y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (STLD 0x2b088 m1 x1 bc st2 st1 ptr j x24 x25 x26 x27 (Z_to_bv 64 flag) x31).
  Proof.
    intros until x31; intros I PLO PHI FLR HJ KD KT. open_fh HY. pose proof I as I0. open_fdcu I0.
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
  Lemma fd1_head : forall m1 out x1 bc st2 st1 cont pad ptr j x23 x24 x25 x26 x27 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j <= cap ->
    (forall m2 bc' ptr' cont' y1 y24 y25 y26 y27 y28 y31, FDCm out st1 st2 cont' bc' pad ptr' m2 -> 0 <= bc' <= 64 ->
       8 <= ni /\ SRCI <= ptr' <= SRCI + ni - 8 -> j + 4 <= cap ->
       evt usegs POST (STLD 0x2b0ec m2 y1 bc' st2 st1 ptr' j y24 y25 y26 y27 y28 y31)) ->
    KEXIT ->
    evt usegs POST (STL1 0x2afdc m1 x1 bc st2 st1 ptr j x23 x24 x25 x26 x27 x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV HJ KD KT. open_fh HY. pose proof I as I0. open_fdcu I0.
    pose proof TBL as (TBLEN & TBBY & TBOK).
    assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
    zstep. if_cases K; zify_cond K.
    - (* [comment removed for export] *)
      zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
      assert (QR : 0 <= bc / 8 <= 8 /\ 0 <= bc mod 8 <= 7) by (clear - BCR; Z.div_mod_to_equations; lia).
      remember (bc / 8) as q eqn:EQ.
      zc. zn. zn. zn. zn. zc. zn. zn. zn. zn. zc. zn. zn.
      eapply (fd1_load _ out _ _ st2 st1 _ pad _ j 1); [close_fdcu | lia | lia | lia | lia | |].
      + intros. eapply KD; [eassumption | lia | lia | lia].
      + intros. eapply KT; [eassumption | exact S1 | exact S2 | exact HJ | | lia]. unfold fbit_ok. split; [lia | intros; right; lia].
    - zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        assert (EP : ptr = SRCI) by lia. subst ptr.
        eapply KT; [exact I | exact S1 | exact S2 | exact HJ | | lia]. unfold fbit_ok. split; [lia | intros; left; reflexivity].
      + (* [comment removed for export] *)
        zstep. rewrite (srliw_val bc 3) by lia. rewrite (Z.mod_small bc 4294967296) by lia. change (2^3) with 8.
        assert (QR : 0 <= bc / 8 <= 8 /\ 8 * (bc / 8) <= bc) by (clear - BCR; Z.div_mod_to_equations; lia).
        remember (bc / 8) as q eqn:EQ. clear EQ.
        zc. zn. zn. zn. zn. zc. zn. zstep. if_cases K3; zify_cond K3.
        * zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn. zn. zc. zn. zn. zn. zn.
          eapply (fd1_load _ out _ _ st2 st1 _ pad _ j 1); [close_fdcu | lia | lia | lia | lia | |].
          -- intros. eapply KD; [eassumption | lia | lia | lia].
          -- intros. eapply KT; [eassumption | exact S1 | exact S2 | exact HJ | | lia]. unfold fbit_ok. split; [lia | intros; right; lia].
        * (* [comment removed for export] *)
          assert (DR : 1 <= ptr - SRCI <= 7 /\ 8 <= ni) by (clear - PV K K2 K3 QR; lia).
          zn. zn. zn. zc. zn. zn. zn. zc. zn. zn. zn. zn. zn. zc. zn. zn. zn. zn.
          eapply (fd1_load _ out _ _ st2 st1 _ pad _ j 0); [close_fdcu | lia | lia | lia | lia | |].
          -- intros. exfalso; lia.
          -- intros. eapply KT; [eassumption | exact S1 | exact S2 | exact HJ | | lia]. unfold fbit_ok. split; [lia | intros; left; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fd1_loop : forall (f : nat) m1 out x1 bc st2 st1 cont pad ptr j x23 x24 x25 x26 x27 x31,
    cap - j <= 4 * Z.of_nat f ->
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> 0 <= j <= cap -> KEXIT ->
    evt usegs POST (STL1 0x2afdc m1 x1 bc st2 st1 ptr j x23 x24 x25 x26 x27 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros HF I S1 S2 BCR PV HJ KT.
    - eapply fd1_head; [exact I | exact S1 | exact S2 | exact BCR | exact PV | exact HJ | intros; exfalso; lia | exact KT].
    - eapply fd1_head; [exact I | exact S1 | exact S2 | exact BCR | exact PV | exact HJ | | exact KT].
      intros m2 bc' ptr' cont' y1 y24 y25 y26 y27 y28 y31 I' B' P' J4.
      eapply fd1_dec; [exact I' | exact S1 | exact S2 | exact B' | lia | exact J4 |].
      intros m3 out' bc2 st2' st1' z1 z23 z24 z25 z26 z27 z31 I2 S1' S2' B2. split.
      + intros LE. eapply IH; [lia | exact I2 | exact S1' | exact S2' | lia | right; exact P' | lia | exact KT].
      + intros GT. open_fh HY. pose proof I2 as I3. open_fdcu I3. pose proof TBL as (TBLEN & TBBY & TBOK).
        assert (P2 : 1 <= 2^tl <= 512) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 512 with (2^9); apply Z.pow_le_mono_r; lia]).
        zn. zn. zn.
        eapply (KT _ out' bc2 st2' st1' cont' pad _ (j + 4)); [close_fdcu | exact S1' | exact S2' | lia | | lia].
        unfold fbit_ok. split; [lia | intros; lia].
  Qed.

  Lemma fd1_start : forall m1 out x1 bc st2 st1 cont pad ptr x23 x24 x25 x26 x27 x31,
    FDCm out st1 st2 cont bc pad ptr m1 -> 0 <= st1 < 2^tl -> 0 <= st2 < 2^tl ->
    0 <= bc <= 64 -> (ptr = SRCI \/ (8 <= ni /\ SRCI <= ptr <= SRCI + ni - 8)) -> KEXIT ->
    evt usegs POST
      (STF 0x2afdc m1 x1 (Z_to_bv 64 (-4)) (Z_to_bv 64 (-5)) (Z_to_bv 64 64) (Z_to_bv 64 DST) (Z_to_bv 64 2305843009213693952) (Z_to_bv 64 (SRCI + 8))
           (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 SRCI) (Z_to_bv 64 ptr) (Z_to_bv 64 (-3))
           (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 65535) (Z_to_bv 64 FBITMASK) (Z_to_bv 64 DST) (Z_to_bv 64 (DST + cap + -3)) x23
           x24 x25 x26 x27 (Z_to_bv 64 bc) (Z_to_bv 64 st2) (Z_to_bv 64 st1) x31).
  Proof.
    intros until x31; intros I S1 S2 BCR PV KT. open_fh HY.
    pose proof (fd1_loop (Z.to_nat cap) m1 out x1 bc st2 st1 cont pad ptr 0 x23 x24 x25 x26 x27 x31) as L.
    replace (DST + 0) with DST in L by lia.
    apply L; [lia | exact I | exact S1 | exact S2 | exact BCR | exact PV | lia | exact KT].
  Qed.
End L1.
