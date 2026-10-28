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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bpure AF_huf_x2t_bl2i AF_huf_x2t_bex AF_huf_x2t_bk0 AF_huf_x2t_bk3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
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
  Notation XS1 w := (xs1 rank w).
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

  Notation STKD mm w minW len st s sv d1 d3 d4 d5 v344 dt xra x5 x6 x7 xa0 xa2 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt mm ->
     evtF bsegs RNG POST
       (ST 0x828d4 mm xra x5 x6 x7 xa0 (Z_to_bv 64 d1) xa2 (Z_to_bv 64 d3) (Z_to_bv 64 d4) (Z_to_bv 64 d5) xa6 xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) (Z_to_bv 64 WK) (Z_to_bv 64 (18446744073709551615 - (WK + 676))) xs6 (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (4 * st)) (Z_to_bv 64 sv)
           xs10 xs11 x28 x29 x30 x31)) (only parsing).
  Notation STD mm w minW len st s sv d1 d3 d4 d5 skip i dt xa0 xa2 xa7 xs4 x28 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 skip) dt mm ->
     evtF bsegs RNG POST
       (ST 0x82910 mm (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 (DT + 20 + 4 * i)) (Z_to_bv 64 (DT + 27 + 4 * i)) (Z_to_bv 64 (DT + 20 + 4 * i))
           xa0 (Z_to_bv 64 d1) xa2 (Z_to_bv 64 d3) (Z_to_bv 64 d4) (Z_to_bv 64 d5) (Z_to_bv 64 (DT + 4 + 4 * i)) xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) xs4 (Z_to_bv 64 (18446744073709551615 - (WK + 676))) (Z_to_bv 64 (DT + 12 + 4 * i)) (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (4 * st)) (Z_to_bv 64 sv)
           (Z_to_bv 64 (DT + 11 + 4 * i)) (Z_to_bv 64 i) x28 (Z_to_bv 64 (DT + 19 + 4 * i)) (Z_to_bv 64 (DT + 35 + 4 * i)) (Z_to_bv 64 (DT + 28 + 4 * i)))) (only parsing).
  Notation STDM mm w minW len st s sv d1 d3 d4 d5 skip i dt xa0 xa7 xs4 :=
    (XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 skip) dt mm ->
     evtF bsegs RNG POST
       (ST 0x82998 mm (Z_to_bv 64 (DT + 4 + 4 * i)) (Z_to_bv 64 (DT + 20 + 4 * i)) (Z_to_bv 64 (DT + 27 + 4 * i)) (Z_to_bv 64 (DT + 20 + 4 * i))
           xa0 (Z_to_bv 64 d1) (Z_to_bv 64 (DT + 4 + 4 * st + 4 * i + 16)) (Z_to_bv 64 d3) (Z_to_bv 64 d4) (Z_to_bv 64 d5) (Z_to_bv 64 (DT + 4 + 4 * i)) xa7
           (Z_to_bv 64 (DT + 4 + 4 * st)) xs4 (Z_to_bv 64 (18446744073709551615 - (WK + 676))) (Z_to_bv 64 (DT + 12 + 4 * i)) (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (4 * st)) (Z_to_bv 64 sv)
           (Z_to_bv 64 (DT + 11 + 4 * i)) (Z_to_bv 64 i) (Z_to_bv 64 (DT + 4 + 4 * st + 4 * i)) (Z_to_bv 64 (DT + 19 + 4 * i)) (Z_to_bv 64 (DT + 35 + 4 * i)) (Z_to_bv 64 (DT + 28 + 4 * i)))) (only parsing).

  Lemma x2_skdr2A : forall m1 (dt : list Z) (w minW len st s sv d1 d3 d4 d5 skip i : Z) xa0 xa7 xs4,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> skbytes (tl + 1 - w) sv d1 d3 d4 d5 ->
    0 <= i < skip -> skip <= len -> i + 8 <= len -> x2pref TT (st + i + 4) dt ->
    (forall m2 (dt' : list Z) ya0 ya2 ya7 y28, i + 8 < skip -> x2pref TT (st + i + 8) dt' ->
       STD m2 w minW len st s sv d1 d3 d4 d5 skip (i + 8) dt' ya0 ya2 ya7 (Z_to_bv 64 WK) y28) ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31, skip <= i + 8 -> x2pref TT (st + i + 8) dt' ->
       STJ m2 w minW len st s sv (Z_to_bv 64 skip) dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    STDM m1 w minW len st s sv d1 d3 d4 d5 skip i dt xa0 xa7 xs4.
  Proof.
    intros until xs4; intros HW HLE HLEN HMIN M2 ST0 ST1 SV SKB HI HSK HI8 PRE KN KJ I.
    open_xbb I. pose proof HY as HY'. open_hx2b HY'.
    pose proof (AF_huf_x2t_bl2i.x2_unp_dtM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UDT m1 MU) as UDT1.
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof SKB as SKB'. destruct SKB' as (_ & _ & _ & _ & _ & _ & _ & _ & R1 & R3 & R4 & R5).
    assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    unfold KHIGH in KLO.
    assert (RSDT2 : rng RNG (shad DT) ((DT + 4 * (1 + 2 ^ mtl) + 7) / 8 - DT / 8))
      by (eapply rng_sub; [exact RSDT | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSDT.
    pose proof ABD as ABDu. unfold ablk, AIMG_HI, KLS in ABDu.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    assert (STX : 0 <= 2 ^ mtl - st - i - 8 <= 4096) by lia.
    change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2KHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2KHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2KHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (u8arr bsegs m1 (WK + 736) syb) with (X2KHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
    change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2KHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2KHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
    repeat match goal with H : ?A \/ ?B |- _ => change (X2KHide (A \/ B)) in H end.
    assert (RSPA : rng RNG SPA 408) by (eapply rng_sub; [exact RSTK | lia | lia]).
    destruct (Z_lt_ge_dec (i + 8) skip) as [HLT | HGE].
    - (kx_runFmd [0x82910] 120%nat [true]
        ([KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange SPA (KHIGH + 5408) (2^47 - 528); KZRange sv 0 255; KZRange st 0 4088;
          KZRange i 0 4088; KZRange skip 1 4096; KZRange (2 ^ mtl - st - i - 8) 0 4096; KZAlign DT 4;
          KZRange d1 0 (2^64 - 1); KZRange d3 0 (2^64 - 1); KZRange d4 0 (2^64 - 1); KZRange d5 0 (2^64 - 1);
          KZWord (SPA + 344) 8 skip; KZWord (SPA + 352) 8 WK;
          KZWr (DT + 4 + 4 * st + 4 * i + 16) 16])
        [(DT + 4 + 4 * st + 4 * i + 16, 16)] [(DT + 4 + 4 * st + 4 * i + 16, 16)] [(DT, 4 * (1 + 2 ^ mtl))]).
      all: try (unfold KHIGH; lia).
      all: try (lazymatch goal with |- flat _ _ _ /\ _ => idtac end; unfold X2KHide in ABDu; x2k_fl).
      all: try (lazymatch goal with |- accP _ _ _ =>
        unfold accP, adenot; cbn [a_base a_off fst snd]; x2e_ez; unfold PropExec.v_addi;
        rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite !Z.mod_small by lia;
        apply (proj2 (proj2 RSPA)); cbn [Z.of_nat]; lia end).
      all: try (lazymatch goal with |- branch_taken BC_LT _ _ = _ =>
        unfold branch_taken; x2e_ez; unfold bv_lts; rewrite !Z_to_bv_signed;
        rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn [Z.of_N]; lia);
        first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia] end).
      kx_post_regs.
      unfold X2KHide in HWC, RK, RS0, SYC, RV, NBC.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
       lazymatch lg with [SE ?a1 _ ?v1; SE ?a2 _ ?v2; SE ?a3 _ ?v3; SE ?a4 _ ?v4; SE ?a5 _ ?v5; SE ?a6 _ ?v6; SE ?a7 _ ?v7; SE ?a8 _ ?v8] =>
        assert (EA1 : estart E a1 = DT + 4 * (st + i + 7) + 6) by x2k_es;
        assert (EA2 : estart E a2 = DT + 4 * (st + i + 7) + 4) by x2k_es;
        assert (EA3 : estart E a3 = DT + 4 * (st + i + 6) + 6) by x2k_es;
        assert (EA4 : estart E a4 = DT + 4 * (st + i + 6) + 4) by x2k_es;
        assert (EA5 : estart E a5 = DT + 4 * (st + i + 5) + 6) by x2k_es;
        assert (EA6 : estart E a6 = DT + 4 * (st + i + 5) + 4) by x2k_es;
        assert (EA7 : estart E a7 = DT + 4 * (st + i + 4) + 6) by x2k_es;
        assert (EA8 : estart E a8 = DT + 4 * (st + i + 4) + 4) by x2k_es;
        pose proof (kx_u8arr_replay bsegs E m1 lg DT _ DTC KXLF) as DTC';
        pose proof (kx_rw_cells_log bsegs E m1 lg _ _ FR KXLF) as FR';
        pose proof (kx_rw_cells_log bsegs E m1 lg _ _ NBC KXLF) as NBC';
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 HWC) KXLF) as HWC1;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RK) KXLF) as RK1;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RS0) KXLF) as RS01;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 SYC) KXLF) as SYC1;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RV) KXLF) as RV1;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 HWC)) as HWC2;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RK)) as RK2;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RS0)) as RS02;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 SYC)) as SYC2;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RV)) as RV2;
        pose proof (kx_stk_log bsegs E m1 lg _ _ WKR) as WKR';
        pose proof (kx_stk_log bsegs E m1 lg _ _ STK) as STK';
        pose proof (kx_mem_inv_log bsegs E m1 lg MI KXLF) as MI';
        pose proof (kx_munch_log E _ m5 m1 lg MU KXLF) as MU';
        pose proof (kx_wmono_log bsegs E m5 m1 lg WM) as WM';
        cbn [log_apart log_inside log_wr] in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
        rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5, ?EA6, ?EA7, ?EA8 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
        cbn [replay] in DTC'; rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5, ?EA6, ?EA7, ?EA8 in DTC';
        cbn [edenot] in DTC'; rewrite !KXA in DTC' by (cbn [length]; lia); cbn [nth] in DTC'
       end
      end.
      change (Z.of_nat 2) with 2 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU'.
      assert (LHWm : zlen (map (Z_to_bv 8) hw) <= 256) by (rewrite length_map; lia).
      assert (LRKm : Z.of_nat (length (u32s (map (Z_to_bv 64) rank))) <= 52) by (rewrite u32s_length, length_map; lia).
      assert (LRSm : Z.of_nat (length (u32s (map (Z_to_bv 64) rs0))) = 60) by (rewrite u32s_length, length_map; lia).
      assert (LRVm : Z.of_nat (length (u32s (map (Z_to_bv 64) rv))) = 624) by (rewrite u32s_length, length_map; lia).
      specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; clear - SDS ST0 HI STX P2 DTL SPAB LOS SPT; unfold X2KHide in *; lia)).
      specialize (NBC' ltac:(cbn [cells_size csize Nat.add length]; repeat split; clear - DFD ST0 HI STX P2 DTL; unfold X2KHide in *; lia)).
      specialize (HWC1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LHWm; unfold X2KHide in *; lia)).
      specialize (RK1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LRKm; unfold X2KHide in *; lia)).
      specialize (RS01 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LRSm; unfold X2KHide in *; lia)).
      specialize (SYC1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR SYLEN; unfold X2KHide in *; lia)).
      specialize (RV1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LRVm; unfold X2KHide in *; lia)).
      pose proof (proj2 (proj2 (proj2 DTC))) as WDT.
      rewrite length_map in WDT.
      specialize (MI' ltac:(repeat split; try exact Logic.I; intros j Hj;
        lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WDT; lia end)).
      specialize (MU' ltac:(repeat split; try exact Logic.I; cbn [inside]; left; lia)).
      lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (BIG := b1) in DTC' end.
      destruct (x2e_dt_of BIG) as [DTE DTBY'].
      rewrite <- DTE in DTC'.
      assert (LB1 : zlen (map bv_unsigned BIG) = 4 * (1 + 2 ^ mtl))
        by (unfold BIG; rewrite length_map, !replay1_length, length_map; exact DTLEN).
      assert (NB : 0 <= tl + 1 - w <= TT) by lia.
      destruct SKB as (S1a & S1b & S5a & S5b & S4a & S4b & S3a & S3b & _).
      assert (PRE0 : x2pref TT (st + i + 4) (map bv_unsigned (map (Z_to_bv 8) dt))) by (rewrite x2k_mm by exact DTBY; exact PRE).
      assert (LD : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
      assert (PRE8 : x2pref TT (st + i + 8) (map bv_unsigned BIG))
        by (unfold BIG;
            replace (st + i + 8) with (st + i + 7 + 1) by lia; apply x2k_c1_step; [lia | rewrite !replay1_length; lia | | lia | lia | lia | apply length_wtlb];
            replace (st + i + 7) with (st + i + 6 + 1) by lia; apply x2k_c1_step; [lia | rewrite !replay1_length; lia | | lia | lia | lia | apply length_wtlb];
            replace (st + i + 6) with (st + i + 5 + 1) by lia; apply x2k_c1_step; [lia | rewrite !replay1_length; lia | | lia | lia | lia | apply length_wtlb];
            replace (st + i + 5) with (st + i + 4 + 1) by lia; apply x2k_c1_step; [lia | lia | exact PRE0 | lia | lia | lia | apply length_wtlb]).
      eapply evtF_eq; [| eapply (KN _ (map bv_unsigned BIG) _ _ _ _ HLT PRE8)].
      2: eapply XBB_close; [exact DTC' | exact LB1 | exact DTBY' | exact (conj HWC1 HWC2) | exact (conj RK1 RK2) | exact (conj RS01 RS02)
           | exact RS0LEN | exact RS0NN | exact (conj SYC1 SYC2) | exact SYLEN | exact (conj RV1 RV2) | exact RVLEN | exact RVNN
           | exact WKR' | exact NBC' | exact STK' | exact MI' | exact MU' | exact WM' | exact FR'].
      1: repeat (lazymatch goal with |- Z_to_bv _ _ = Z_to_bv _ _ => fail | _ => f_equal end).
      all: try (f_equal; clear; lia).
      apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      rewrite <- (Z_mod_plus_full (- WK + -677) 1 (2 ^ Z.of_N 64)). f_equal. clear; lia.
    - (kx_runFmd [0x82abc] 120%nat [false]
        ([KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange SPA (KHIGH + 5408) (2^47 - 528); KZRange sv 0 255; KZRange st 0 4088;
          KZRange i 0 4088; KZRange skip 1 4096; KZRange (2 ^ mtl - st - i - 8) 0 4096; KZAlign DT 4;
          KZRange d1 0 (2^64 - 1); KZRange d3 0 (2^64 - 1); KZRange d4 0 (2^64 - 1); KZRange d5 0 (2^64 - 1);
          KZWord (SPA + 344) 8 skip; KZWord (SPA + 352) 8 WK;
          KZWr (DT + 4 + 4 * st + 4 * i + 16) 16])
        [(DT + 4 + 4 * st + 4 * i + 16, 16)] [(DT + 4 + 4 * st + 4 * i + 16, 16)] [(DT, 4 * (1 + 2 ^ mtl))]).
      all: try (unfold KHIGH; lia).
      all: try (lazymatch goal with |- flat _ _ _ /\ _ => idtac end; unfold X2KHide in ABDu; x2k_fl).
      all: try (lazymatch goal with |- accP _ _ _ =>
        unfold accP, adenot; cbn [a_base a_off fst snd]; x2e_ez; unfold PropExec.v_addi;
        rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; rewrite !Z.mod_small by lia;
        apply (proj2 (proj2 RSPA)); cbn [Z.of_nat]; lia end).
      all: try (lazymatch goal with |- branch_taken BC_LT _ _ = _ =>
        unfold branch_taken; x2e_ez; unfold bv_lts; rewrite !Z_to_bv_signed;
        rewrite !bv_swrap_small by (unfold bv_half_modulus, bv_modulus; cbn [Z.of_N]; lia);
        first [apply Z.ltb_lt; lia | apply Z.ltb_ge; lia] end).
      kx_post_regs.
      unfold X2KHide in HWC, RK, RS0, SYC, RV, NBC.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
       lazymatch lg with [SE ?a1 _ ?v1; SE ?a2 _ ?v2; SE ?a3 _ ?v3; SE ?a4 _ ?v4; SE ?a5 _ ?v5; SE ?a6 _ ?v6; SE ?a7 _ ?v7; SE ?a8 _ ?v8] =>
        assert (EA1 : estart E a1 = DT + 4 * (st + i + 7) + 6) by x2k_es;
        assert (EA2 : estart E a2 = DT + 4 * (st + i + 7) + 4) by x2k_es;
        assert (EA3 : estart E a3 = DT + 4 * (st + i + 6) + 6) by x2k_es;
        assert (EA4 : estart E a4 = DT + 4 * (st + i + 6) + 4) by x2k_es;
        assert (EA5 : estart E a5 = DT + 4 * (st + i + 5) + 6) by x2k_es;
        assert (EA6 : estart E a6 = DT + 4 * (st + i + 5) + 4) by x2k_es;
        assert (EA7 : estart E a7 = DT + 4 * (st + i + 4) + 6) by x2k_es;
        assert (EA8 : estart E a8 = DT + 4 * (st + i + 4) + 4) by x2k_es;
        pose proof (kx_u8arr_replay bsegs E m1 lg DT _ DTC KXLF) as DTC';
        pose proof (kx_rw_cells_log bsegs E m1 lg _ _ FR KXLF) as FR';
        pose proof (kx_rw_cells_log bsegs E m1 lg _ _ NBC KXLF) as NBC';
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 HWC) KXLF) as HWC1;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RK) KXLF) as RK1;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RS0) KXLF) as RS01;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 SYC) KXLF) as SYC1;
        pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RV) KXLF) as RV1;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 HWC)) as HWC2;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RK)) as RK2;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RS0)) as RS02;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 SYC)) as SYC2;
        pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 RV)) as RV2;
        pose proof (kx_stk_log bsegs E m1 lg _ _ WKR) as WKR';
        pose proof (kx_stk_log bsegs E m1 lg _ _ STK) as STK';
        pose proof (kx_mem_inv_log bsegs E m1 lg MI KXLF) as MI';
        pose proof (kx_munch_log E _ m5 m1 lg MU KXLF) as MU';
        pose proof (kx_wmono_log bsegs E m5 m1 lg WM) as WM';
        cbn [log_apart log_inside log_wr] in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
        rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5, ?EA6, ?EA7, ?EA8 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
        cbn [replay] in DTC'; rewrite ?EA1, ?EA2, ?EA3, ?EA4, ?EA5, ?EA6, ?EA7, ?EA8 in DTC';
        cbn [edenot] in DTC'; rewrite !KXA in DTC' by (cbn [length]; lia); cbn [nth] in DTC'
       end
      end.
      change (Z.of_nat 2) with 2 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU'.
      assert (LHWm : zlen (map (Z_to_bv 8) hw) <= 256) by (rewrite length_map; lia).
      assert (LRKm : Z.of_nat (length (u32s (map (Z_to_bv 64) rank))) <= 52) by (rewrite u32s_length, length_map; lia).
      assert (LRSm : Z.of_nat (length (u32s (map (Z_to_bv 64) rs0))) = 60) by (rewrite u32s_length, length_map; lia).
      assert (LRVm : Z.of_nat (length (u32s (map (Z_to_bv 64) rv))) = 624) by (rewrite u32s_length, length_map; lia).
      specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; clear - SDS ST0 HI STX P2 DTL SPAB LOS SPT; unfold X2KHide in *; lia)).
      specialize (NBC' ltac:(cbn [cells_size csize Nat.add length]; repeat split; clear - DFD ST0 HI STX P2 DTL; unfold X2KHide in *; lia)).
      specialize (HWC1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LHWm; unfold X2KHide in *; lia)).
      specialize (RK1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LRKm; unfold X2KHide in *; lia)).
      specialize (RS01 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LRSm; unfold X2KHide in *; lia)).
      specialize (SYC1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR SYLEN; unfold X2KHide in *; lia)).
      specialize (RV1 ltac:(repeat split; clear - DTWK ST0 HI STX P2 DTL WKL WR LRVm; unfold X2KHide in *; lia)).
      pose proof (proj2 (proj2 (proj2 DTC))) as WDT.
      rewrite length_map in WDT.
      specialize (MI' ltac:(repeat split; try exact Logic.I; intros j Hj;
        lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by lia; apply WDT; lia end)).
      specialize (MU' ltac:(repeat split; try exact Logic.I; cbn [inside]; left; lia)).
      lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (BIG := b1) in DTC' end.
      destruct (x2e_dt_of BIG) as [DTE DTBY'].
      rewrite <- DTE in DTC'.
      assert (LB1 : zlen (map bv_unsigned BIG) = 4 * (1 + 2 ^ mtl))
        by (unfold BIG; rewrite length_map, !replay1_length, length_map; exact DTLEN).
      assert (NB : 0 <= tl + 1 - w <= TT) by lia.
      destruct SKB as (S1a & S1b & S5a & S5b & S4a & S4b & S3a & S3b & _).
      assert (PRE0 : x2pref TT (st + i + 4) (map bv_unsigned (map (Z_to_bv 8) dt))) by (rewrite x2k_mm by exact DTBY; exact PRE).
      assert (LD : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
      assert (PRE8 : x2pref TT (st + i + 8) (map bv_unsigned BIG))
        by (unfold BIG;
            replace (st + i + 8) with (st + i + 7 + 1) by lia; apply x2k_c1_step; [lia | rewrite !replay1_length; lia | | lia | lia | lia | apply length_wtlb];
            replace (st + i + 7) with (st + i + 6 + 1) by lia; apply x2k_c1_step; [lia | rewrite !replay1_length; lia | | lia | lia | lia | apply length_wtlb];
            replace (st + i + 6) with (st + i + 5 + 1) by lia; apply x2k_c1_step; [lia | rewrite !replay1_length; lia | | lia | lia | lia | apply length_wtlb];
            replace (st + i + 5) with (st + i + 4 + 1) by lia; apply x2k_c1_step; [lia | lia | exact PRE0 | lia | lia | lia | apply length_wtlb]).
      eapply evtF_eq; [| eapply (KJ _ (map bv_unsigned BIG) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) PRE8)].
      2: eapply XBB_close; [exact DTC' | exact LB1 | exact DTBY' | exact (conj HWC1 HWC2) | exact (conj RK1 RK2) | exact (conj RS01 RS02)
           | exact RS0LEN | exact RS0NN | exact (conj SYC1 SYC2) | exact SYLEN | exact (conj RV1 RV2) | exact RVLEN | exact RVNN
           | exact WKR' | exact NBC' | exact STK' | exact MI' | exact MU' | exact WM' | exact FR'].
      1: repeat (lazymatch goal with |- Z_to_bv _ _ = Z_to_bv _ _ => fail | _ => f_equal end).
      all: try (f_equal; clear; lia).
      apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      rewrite <- (Z_mod_plus_full (- WK + -677) 1 (2 ^ Z.of_N 64)). f_equal. clear; lia.
  Qed.

  Lemma x2_skdrA : forall m1 (dt : list Z) (w minW len st s sv d1 d3 d4 d5 skip i : Z) xa0 xa2 xa7 xs4 x28,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> skbytes (tl + 1 - w) sv d1 d3 d4 d5 ->
    0 <= i < skip -> skip <= len -> i + 8 <= len -> x2pref TT (st + i) dt ->
    (forall m2 (dt' : list Z) ya0 ya2 ya7 y28, i + 8 < skip -> x2pref TT (st + i + 8) dt' ->
       STD m2 w minW len st s sv d1 d3 d4 d5 skip (i + 8) dt' ya0 ya2 ya7 (Z_to_bv 64 WK) y28) ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31, skip <= i + 8 -> x2pref TT (st + i + 8) dt' ->
       STJ m2 w minW len st s sv (Z_to_bv 64 skip) dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    STD m1 w minW len st s sv d1 d3 d4 d5 skip i dt xa0 xa2 xa7 xs4 x28.
  Proof.
    intros until x28; intros HW HLE HLEN HMIN M2 ST0 ST1 SV SKB HI HSK HI8 PRE KN KJ.
    eapply AF_huf_x2t_bk3.x2_skdr1A; [eassumption .. | intros until ys4; intros PRE1].
    eapply x2_skdr2A; [exact HW | exact HLE | exact HLEN | exact HMIN | exact M2 | exact ST0 | exact ST1 | exact SV | exact SKB | exact HI | exact HSK | exact HI8 | exact PRE1 | exact KN | exact KJ].
    Unshelve. all: assumption.
  Qed.

  End FX.
  End FM.
End X2B.
End CANSEC1.
