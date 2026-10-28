(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bpure.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Section G.
  Variables (RNG : footprint) (m5 : amem) (SPV SPA lo DT WK wksz FF mtl : Z).
  Hypothesis HY : x2B_hyps RNG SPV SPA lo DT WK wksz FF mtl.
  Hypothesis UDT : unpoisoned m5 DT (DT + 4 * (1 + 2 ^ mtl)).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : x2hb_art m5.
  Lemma x2_mtl : 1 <= mtl <= 12.
  Proof. open_hx2b HY. exact MTL. Qed.
  Lemma x2_bands : (DT + 4 * (1 + 2 ^ mtl) + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (WK + wksz + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= WK)
                   /\ 0x10007fff8000 + 5408 <= SPA /\ SPA + 528 <= 2^47 /\ 0x60f000 <= DT /\ 0x60f000 <= WK
                   /\ FF + 64 + 4096 <= lo /\ (FF + 64 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= FF).
  Proof.
    open_hx2b HY. clear SDS SWS DTWK DFD DFW.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABD, ABW, ABF. unfold KHIGH in KLO.
    repeat split; try lia.
  Qed.
  Lemma x2_rsta : rng RNG (SPA - 112) 520.
  Proof. open_hx2b HY. eapply rng_sub'; [exact RSTK| lia]. Qed.
  Lemma x2_unp_dtM : forall m1, munch [(DT, DT + 4 * (1 + 2 ^ mtl)); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1 -> unpoisoned m1 DT (DT + 4 * (1 + 2 ^ mtl)).
  Proof.
    intros m1 MU. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    open_hx2b HY. pose proof (x2b_dtbB mtl MTL) as (DTBR & P2R).
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *.
    set (DTB := 4 * (1 + 2 ^ mtl)) in *. clearbody DTB.
    clear - B1 B2 B3 B4 B5 B6 DTBR DTL DTH WKL WKH WR KLO LOS SPAB SPT.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2_unp_wkM : forall m1, munch [(DT, DT + 4 * (1 + 2 ^ mtl)); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1 -> unpoisoned m1 WK (WK + wksz).
  Proof.
    intros m1 MU. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UW | exact MU |].
    open_hx2b HY. pose proof (x2b_dtbB mtl MTL) as (DTBR & P2R).
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF, KHIGH in *.
    set (DTB := 4 * (1 + 2 ^ mtl)) in *. clearbody DTB.
    clear - B1 B2 B3 B4 B5 B6 DTBR DTL DTH WKL WKH WR KLO LOS SPAB SPT.
    repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2_artM : forall m1, munch [(DT, DT + 4 * (1 + 2 ^ mtl)); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1 -> wmono bsegs m5 m1 -> x2hb_art m1.
  Proof.
    intros m1 MU WM. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply x2hb_art_transport; [exact ART0| exact MU| exact WM|]. open_hx2b HY. unfold KHIGH in KLO.
    repeat constructor; cbn [fst]; lia.
  Qed.
  Lemma x2_helper_hyps : x2hb_hyps RNG SPA DT (WK + 736) mtl.
  Proof.
    pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8). pose proof x2_rsta as RSTA.
    open_hx2b HY. pose proof (x2b_dtbB mtl MTL) as (DTBR & P2R). unfold x2hb_hyps.
    set (DTB := 4 * (1 + 2 ^ mtl)) in *. clearbody DTB.
    assert (A0 : rng RNG (shad DT) (shspan DT DTB))
      by (eapply rng_sub; [exact RSDT| lia| unfold shspan; rewrite nshad_div; clear - DTL DTBR; Z.div_mod_to_equations; lia]).
    assert (A1 : 4096 <= WK + 736) by lia. assert (A2 : WK + 736 + 256 < 2^47) by lia.
    assert (A3 : KHIGH <= SPA - 112) by (unfold KHIGH in *; lia). assert (A4 : SPA + 16 <= 2^47) by lia.
    assert (A5 : SPA mod 16 = 0) by (clear - SPA32; Z.div_mod_to_equations; lia).
    assert (A6 : DT + DTB <= WK + 736 \/ WK + 736 + 256 <= DT) by (clear - DTWK WR; lia).
    assert (A7 : DT + DTB <= SPA - 112 \/ SPA <= DT) by (clear - SDS LOS SPAB; lia).
    assert (A8 : WK + 736 + 256 <= SPA - 112 \/ SPA <= WK + 736) by (clear - SWS LOS SPAB WR; lia).
    assert (A9 : ablk (WK + 736) (WK + 736 + 256)) by (eapply ablk_sub; [exact ABW| lia| lia]).
    assert (A10 : rng RNG (WK + 736) 256) by (eapply rng_sub; [exact RW| lia| lia]).
    assert (A11 : rng RNG (shad (WK + 736)) (shspan (WK + 736) 256))
      by (eapply rng_sub; [exact RSW| |]; rewrite ?shad_div; unfold shspan; rewrite ?nshad_div; clear - WKL WR; Z.div_mod_to_equations; lia).
    assert (A12 : rng RNG (SPA - 112) 112) by (eapply rng_sub; [exact RSTA| lia| lia]).
    exact (conj DTL (conj DTH (conj DT4 (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8
          (conj ABD (conj RDT (conj A0 (conj A9 (conj A10 (conj A11 (conj A12 RI)))))))))))))))))).
  Qed.
End G.

Section X2B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT WK wksz FF hdw r mtl : Z).
  Hypothesis HY : x2B_hyps RNG SPV SPA lo DT WK wksz FF mtl.
  Hypothesis UDT : unpoisoned m5 DT (DT + 4 * (1 + 2 ^ mtl)).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : x2hb_art m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Hypothesis HM : hdw mod 256 = mtl.
  Hypothesis HR : 0 <= hdw < 2^32.
  Hypothesis TP : tp = Z_to_bv 64 ATP.
  Hypothesis X2HB : x2hb_stmt.
  Variable POST : machine_state -> Prop.
  Local Ltac x2_reunp :=
    repeat match goal with H : unpoisoned ?mx _ _ |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    try match goal with H : x2hb_art ?mx |- _ => lazymatch mx with m5 => fail | _ => clear H end end;
    lazymatch goal with
    | MU : munch _ m5 ?m2 |- _ =>
        pose proof (x2_unp_dtM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UDT m2 MU) as UDT1;
        pose proof (x2_unp_wkM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UW m2 MU) as UW1;
        try lazymatch goal with WM : wmono _ m5 m2 |- _ => pose proof (x2_artM RNG m5 SPV SPA lo DT WK wksz FF mtl HY ART0 m2 MU WM) as ART1 end
    | |- _ => idtac
    end.
  Local Ltac x2_open :=
    open_hx2b HY; unfold KHIGH in *;
    pose proof (x2_bands RNG SPV SPA lo DT WK wksz FF mtl HY) as (BDT & BWK & BSP & BSP2 & B5 & B6 & B7 & BFF);
    pose proof (x2_rsta RNG SPV SPA lo DT WK wksz FF mtl HY) as RSTA;
    pose proof (x2b_dtbB mtl (x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY)) as (DTBR & P2R);
    lazymatch goal with H1 : DT + 4 * (1 + 2 ^ mtl) <= lo \/ SPV <= DT, H2 : WK + wksz <= lo \/ SPV <= WK, H3 : lo <= SPV - 5936, H4 : SPV - 528 <= SPA <= SPV - 512 |- _ =>
      assert (SDSA : DT + 4 * (1 + 2 ^ mtl) <= SPA - 5408 \/ SPA + 408 <= DT) by (clear - H1 H3 H4; lia);
      assert (SWSA : WK + wksz <= SPA - 5408 \/ SPA + 408 <= WK) by (clear - H2 H3 H4; lia) end;
    x2_reunp.
  Notation KZB := [KZRange SPA (0x10007fff8000 + 5408) (2^47 - 528); KZRange SPV (0x10007fff8000 + 5920) (2^47 - 16);
     KZRange DT 0x60f000 (2^47 - 12); KZRange WK 0x60f000 (2^47 - 2124); KZRange wksz 2124 (2^32); KZRange (WK + wksz) 0 (2^47);
     KZRange FF 4096 (2^47); KZRange hdw 0 (2^32); KZRange mtl 1 12; KZRange (2 ^ mtl) 2 4096; KZAlign SPA 32; KZAlign FF 64; KZAlign DT 4; KZAlign WK 4;
     KZDisj DT (4 * (1 + 2 ^ mtl)) (SPA - 112) 520; KZDisj WK wksz (SPA - 112) 520; KZDisj DT (4 * (1 + 2 ^ mtl)) WK wksz;
     KZDisj WK wksz FF 64; KZDisj DT (4 * (1 + 2 ^ mtl)) FF 64; KZDisj (SPA - 112) 520 FF 64] (only parsing).
  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 0x7fff8000) xs4 xs5 xs6 xs7
             xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).
  Variables (hw rank : list Z) (nbs tl : Z).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis TLM : tl <= mtl.
  Notation TT := (TTB tl mtl).
  Lemma TT_range : 1 <= tl <= 12 -> tl <= TT <= mtl /\ Z.min mtl 11 <= TT.
  Proof. intros H. pose proof (x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY). apply TTB_range; lia. Qed.
  Local Ltac x2_fwd L := intros; pose proof (x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY); eapply L; try eassumption; lia.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof. x2_fwd AF_huf_x2t_bpure.rank_small'. Qed.
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
  Lemma rdn_sh0 : forall (m : amem) X n p, unpoisoned m X (X + n) -> X <= p -> p - p mod 8 + 8 <= X + n ->
    rdn bsegs m (wa (shad p)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
  Proof.
    intros m X n p (H0 & H1 & H) Hp Hg. cbn [rdn]. replace (shad p) with (ASHOFF + p / 8) by (rewrite shad_div; lia).
    destruct (H (p / 8) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia))
      as (b & Hb & Hok).
    rewrite Hb. rewrite (gran_ok_full _ _ Hok) by (Z.div_mod_to_equations; lia). reflexivity.
  Qed.
  Notation XS1 w := (xs1 rank w).
  Lemma xs1_bounds : forall w, 1 <= w <= 13 -> 0 <= XS1 w <= 256.
  Proof. x2_fwd AF_huf_x2t_bpure.xs1_bounds'. Qed.
  Variables (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word).
  Variables (xnv xflv : word).
  Section FM.
  Variable maxW : Z.
  Hypothesis HMW : 1 <= maxW <= tl.
  Hypothesis HIGH : forall v, maxW < v <= 12 -> Znth v rank = 0.
  Notation RV0 w := (rv0 rank tl TT w).
  Notation RVC c w := (rvc rank tl TT c w).
  Notation RINV := (AF_huf_x2t_bpure.RINV rank).
  Notation SINV := (AF_huf_x2t_bpure.SINV hw rank nbs maxW).
  Notation RSF := (AF_huf_x2t_bpure.RSF rank maxW).
  Notation VINV := (AF_huf_x2t_bpure.VINV rank tl mtl).
  Notation ROWS := (AF_huf_x2t_bpure.ROWS rank tl mtl maxW).
  Notation RVX := (AF_huf_x2t_bpure.RVX rank tl mtl maxW).
  Lemma sinv0 : forall rs0, RINV (maxW + 1) rs0 -> Znth 1 rs0 = XS1 (maxW + 1) -> SINV 0 rs0.
  Proof. x2_fwd AF_huf_x2t_bpure.sinv0. Qed.
  Lemma sort_unit : forall j rs0, 0 <= j < nbs -> SINV j rs0 -> zlen rs0 = 15 ->
    0 <= Znth j hw <= maxW /\ 0 <= Znth (Znth j hw + 1) rs0 /\ Znth (Znth j hw + 1) rs0 + 1 <= nbs
    /\ SINV (j + 1) (Zupd (Znth j hw + 1) (Znth (Znth j hw + 1) rs0 + 1) rs0).
  Proof. x2_fwd AF_huf_x2t_bpure.sort_unit. Qed.
  Lemma rsf_of_sinv : forall rs0, SINV nbs rs0 -> zlen rs0 = 15 -> RSF (Zupd 1 0 rs0).
  Proof. x2_fwd AF_huf_x2t_bpure.rsf_of_sinv. Qed.
  Lemma rv0_bounds : forall w, 1 <= w <= maxW + 1 -> 0 <= RV0 w <= 2 ^ mtl /\ RV0 (maxW + 1) = 2^TT.
  Proof. x2_fwd AF_huf_x2t_bpure.rv0_bounds. Qed.
  Lemma rows0 : forall c rv, c <= tl + 1 - maxW -> VINV (maxW + 1) rv -> ROWS c 1 rv.
  Proof. x2_fwd AF_huf_x2t_bpure.rows0. Qed.
  Lemma rows_next : forall c rv, ROWS c (maxW + 1) rv -> ROWS (c + 1) 1 rv.
  Proof. x2_fwd AF_huf_x2t_bpure.rows_next. Qed.
  Lemma rvc_val : forall c w, 0 <= c -> 1 <= w <= maxW + 1 -> 0 <= RVC c w <= RV0 w /\ RVC c w = RV0 w / 2^c.
  Proof. x2_fwd AF_huf_x2t_bpure.rvc_val. Qed.
  Lemma rvx_of_rows : forall rv, ROWS (TT - (tl + 1 - maxW) + 1) 1 rv -> RVX rv.
  Proof. x2_fwd AF_huf_x2t_bpure.rvx_of_rows. Qed.
  Lemma l1_facts : forall w e, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> 0 <= e ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 2 ^ mtl /\ 1 <= 2 ^ e <= 2 ^ mtl.
  Proof. x2_fwd AF_huf_x2t_bpure.l1_facts. Qed.
  Section FX.
  Variables (rs0 rv : list Z) (syb : list byte).
  Hypothesis RSFX : RSF rs0.
  Hypothesis RVXX : RVX rv.
  Notation XBF v152 v160 v192 v208 v264 v304 v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank (Z_to_bv 64 (16777216 * (hdw mod 2 ^ 64 / 16777216))) (Z_to_bv 64 mtl) (Z_to_bv 64 r) v24 (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (tl + 1 - TT))
        (Z_to_bv 64 223338299392) (Z_to_bv 64 (18446744073709551615 - (DT + 4))) (Z_to_bv 64 (DT + 12)) (Z_to_bv 64 (DT + 27)) (Z_to_bv 64 (DT + 20)) (Z_to_bv 64 (DT + 19))
        (Z_to_bv 64 (DT + 35)) (Z_to_bv 64 (DT + 28)) (Z_to_bv 64 (DT + 11)) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (18446744073709551615 - WK))
        v152 v160 v192 v208 v224 v232 v240 v248 v256 v264 v272 v280 v288 (Z_to_bv 64 maxW) v304 v312 v320 v328 (Z_to_bv 64 (DT + 4)) v344 v360 (Z_to_bv 64 TT) v376 k384 k392
        dt rs0 syb rv mm) (only parsing).
  Local Ltac fr_norm FR :=
    try replace (Z_to_bv 64 (-1 * TT + tl + 1)) with (Z_to_bv 64 (tl + 1 - TT)) in FR by (f_equal; lia);
    try replace (Z_to_bv 64 (-1 * DT + -5)) with (Z_to_bv 64 (18446744073709551615 - (DT + 4))) in FR by (apply Z_to_bv_eqm; Z.div_mod_to_equations; lia).
  Notation STLE pc mm w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt
           xra x5 x6 x7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
         v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST
       (ST pc mm xra x5 x6 x7 (Z_to_bv 64 (WK + 4 * w)) (Z_to_bv 64 (TT - (tl + 1 - w))) (Z_to_bv 64 (Z.max 1 (tl + 1 - w + (tl + 1 - TT)))) (Z_to_bv 64 (tl + 1 - w))
           (Z_to_bv 64 (4 * w)) (Z_to_bv 64 (18446744073709551615 - WK)) (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (XS1 w))
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STLT mm w v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt
           xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
         v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82560 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Notation XL w minW len v320 v328 v344 dt mm :=
    (XBF (Z_to_bv 64 (w + 1)) (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - w)) (Z_to_bv 64 (tl + 1 - w)) (Z_to_bv 64 w) (Z_to_bv 64 (XS1 (w + 1)))
         (Z_to_bv 64 (4294967296 * (tl + 1 - w))) (Z_to_bv 64 (maxW + 1 - minW)) (Z_to_bv 64 (2 * tl + 2 - w - minW)) (Z_to_bv 64 (4 * minW))
         (Z_to_bv 64 (65536 * (tl + 1 - w) + 16777216)) (Z_to_bv 64 (4 * minW)) (Z_to_bv 64 (WK + 52 * (tl + 1 - w) + 4 * minW))
         (Z_to_bv 64 (tl + 1 - w + (tl + 1 - TT))) (Z_to_bv 64 minW) (Z_to_bv 64 len) v320 v328 v344
         (Z_to_bv 64 (WK + 52 * (tl + 1 - w))) (Z_to_bv 64 (18446744073709551615 - (WK + 52 * (tl + 1 - w)))) dt mm) (only parsing).
  Notation STSH mm w minW len st s v320 v328 v344 dt xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len v320 v328 v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82758 mm xra (Z_to_bv 64 st) x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 s)
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Lemma l2_facts : forall w e minW, 1 <= w <= maxW -> e = TT - (tl + 1 - w) -> tl - maxW + 1 <= e -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    0 <= XS1 w /\ XS1 (w + 1) <= 256 /\ XS1 (w + 1) = XS1 w + Znth w rank /\ 0 <= Znth w rank /\ 0 <= RV0 w
    /\ RV0 (w + 1) = RV0 w + Znth w rank * 2 ^ e /\ RV0 (w + 1) <= 2 ^ mtl /\ 2 <= 2 ^ e <= 2 ^ mtl /\ 1 <= minW <= maxW /\ 1 <= e <= mtl - 1.
  Proof.
    intros w e minW HW HE HLE HMIN. pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    destruct (l1_facts w e HW HE ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    assert (2 <= 2 ^ e) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
    repeat split; try lia.
  Qed.
  Lemma l2x_facts : forall w len minW, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    RV0 (w + 1) = RV0 w + (XS1 (w + 1) - XS1 w) * len /\ 2 <= len <= 2 ^ (mtl - 1) /\ 1 <= minW <= maxW /\ tl + 1 - w + (tl + 1 - TT) <= minW
    /\ RVC (tl + 1 - w) (maxW + 1) = len /\ 0 <= RVC (tl + 1 - w) minW <= len /\ RVC (tl + 1 - w) 1 = 0.
  Proof. x2_fwd AF_huf_x2t_bpure.l2x_facts. Qed.
  Lemma w2_facts : forall w len minW w2 len2, 1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) ->
    minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> minW <= w2 <= maxW -> len2 = 2 ^ (TT - (tl + 1 - w) - (tl + 1 - w2)) ->
    0 <= XS1 w2 /\ XS1 (w2 + 1) <= 256 /\ XS1 (w2 + 1) = XS1 w2 + Znth w2 rank /\ 0 <= Znth w2 rank
    /\ 0 <= RVC (tl + 1 - w) w2 /\ RVC (tl + 1 - w) (w2 + 1) = RVC (tl + 1 - w) w2 + (XS1 (w2 + 1) - XS1 w2) * len2 /\ RVC (tl + 1 - w) (w2 + 1) <= len
    /\ 1 <= len2 <= len /\ 0 <= TT - (tl + 1 - w) - (tl + 1 - w2) <= mtl - 1 /\ RVC (tl + 1 - w) w2 <= len.
  Proof. x2_fwd AF_huf_x2t_bpure.w2_facts. Qed.
  Notation STSK mm w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x827c4 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (4 * st)) (Z_to_bv 64 sv)
           xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STJ mm w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82abc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 (Z_to_bv 64 sv)
           xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STW2 mm w minW len st s sv w2 v344 dt xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82b00 mm xra x5 x6 x7 xa0 (Z_to_bv 64 (4 * w2)) xa2 xa3 xa4 xa5 xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 (Z_to_bv 64 sv)
           (Z_to_bv 64 (2 * tl + 2 - w - w2)) (Z_to_bv 64 (maxW + 1 - w2)) x28 x29 x30 x31)) (only parsing).
  Notation STSL mm w minW len st s v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82ac8 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STLT2 mm w minW len st s v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x82560 mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).

  Lemma signed_small : forall z, -100 <= z <= 100 -> bv_signed (Z_to_bv 64 z) = z.
  Proof.
    intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
    change (2 ^ 63) with 9223372036854775808. destruct (Z.ltb_spec0 (z mod 18446744073709551616) 9223372036854775808); Z.div_mod_to_equations; lia.
  Qed.

  Definition SKA_T : Prop := forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT st dt ->
    (forall m2 (dt' : list Z) (v344' : word) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (st + RVC (tl + 1 - w) minW) dt' ->
       STJ m2 w minW len st s sv v344' dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    STSK m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31.
  Definition JNA_T : Prop := forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT (st + RVC (tl + 1 - w) minW) dt ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (st + len) dt' ->
       STSL m2 w minW len st s v344 dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STJ m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31.
  Definition SLA_T : Prop := forall m1 (dt : list Z) (w minW len st s : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl ->
    (forall y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 < XS1 (w + 1) ->
       STSH m1 w minW len (st + len) (s + 1) (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt xra y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    (forall y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 = XS1 (w + 1) ->
       STLT2 m1 w minW len st s v344 dt xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STSL m1 w minW len st s v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.
  Notation XBW dt mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank (Z_to_bv 64 (16777216 * (hdw mod 2 ^ 64 / 16777216))) (Z_to_bv 64 mtl) (Z_to_bv 64 r) k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112
        (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (18446744073709551615 - WK)) k152 k160 k192 (Z_to_bv 64 tl)
        k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 (Z_to_bv 64 (DT + 4)) k344 k360 (Z_to_bv 64 TT) k376 k384 k392 dt rs0 syb rv mm) (only parsing).
  Notation STQ mm xra x5 x6 x7 xa0 xa1 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 :=
    (ST 0x824b0 mm xra x5 x6 x7 xa0 xa1 (Z_to_bv 64 (TT - tl + maxW)) (Z_to_bv 64 (4294967296 * (maxW + 1))) xa4 xa5 xa6 xa7
        xs2 (Z_to_bv 64 WK) (Z_to_bv 64 maxW) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11
        x28 x29 x30 (Z_to_bv 64 (tl - maxW + 1)))
    (only parsing).
  Notation STEX mm v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt xra x5 x6 x7 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (XBF (Z_to_bv 64 (maxW + 1)) (Z_to_bv 64 (tl + 1 - maxW + (tl + 1 - TT))) (Z_to_bv 64 (2 * tl + 2 - (maxW + 1))) (Z_to_bv 64 (tl + 1 - (maxW + 1))) (Z_to_bv 64 maxW)
         (Z_to_bv 64 (XS1 (maxW + 1))) v24 v224 v232 v240 v248 v256 v272 v280 v288 v312 v320 v328 v344 v360 v376 dt mm ->
     evtF bsegs RNG POST (ST 0x82cac mm xra x5 x6 x7 (Z_to_bv 64 DT) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                            xs2 (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Definition x2_fillsB_stmt : Prop := forall m1 (dt : list Z) xra x5 x6 x7 xa0 xa1 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30,
    XBW dt m1 -> x2pref TT 0 dt ->
    (forall m2 (dt' : list Z) y24 y224 y232 y240 y248 y256 y272 y280 y288 y312 y320 y328 y344 y360 y376
            yra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, x2pref TT (2 ^ TT) dt' ->
       STEX m2 y24 y224 y232 y240 y248 y256 y272 y280 y288 y312 y320 y328 y344 y360 y376 dt' yra y5 y6 y7 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    evtF bsegs RNG POST (STQ m1 xra x5 x6 x7 xa0 xa1 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30).

  End FX.
  End FM.
End X2B.
End CANSEC1.
