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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bpure AF_huf_x2t_bl2i AF_huf_x2t_bex AF_huf_x2t_bk0 AF_huf_x2t_bk1 AF_huf_x2t_bk4.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac x2d_es := unfold estart; cbn [a_base a_off]; x2e_ez; rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus;
  rewrite Z.mod_small by lia; lia.

Ltac x2d_u := rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (Z.of_N 64) with 64;
  rewrite Z.mod_small by lia; lia.

Lemma x2d_fs : forall (pre : list byte) x post, firstn 4 (skipn (length pre) (pre ++ le4 x ++ post)) = le4 x.
Proof. induction pre as [|b pre IH]; intros x post; [reflexivity | exact (IH x post)]. Qed.

Section CANSEC1. Context {rc : runConstT}.
Lemma x2d_rdv : forall m A (rv : list Z) i sx,
  bytes_at bsegs m A (u32s (map (Z_to_bv 64) rv)) -> 0 <= i < Z.of_nat (length rv) -> 0 <= Znth i rv < 2 ^ 31 ->
  rdval bsegs m (wa (A + 4 * i)) 4 sx = Z_to_bv 64 (Znth i rv).
Proof.
  intros m A rv i sx HB HI HV.
  assert (NTH : nth_error (map (Z_to_bv 64) rv) (Z.to_nat i) = Some (Z_to_bv 64 (Znth i rv))).
  { rewrite nth_error_map, (nth_error_nth' rv 0) by lia. reflexivity. }
  destruct (u32s_split _ _ _ NTH) as (pre & post & _ & _ & EQ & LP).
  unfold rdval.
  replace (A + 4 * i) with (A + Z.of_nat (4 * Z.to_nat i)) by lia.
  rewrite (bytes_at_rdn bsegs m A _ (4 * Z.to_nat i) 4 HB) by (rewrite u32s_length, length_map; lia).
  cbv beta iota.
  rewrite EQ, <- LP, x2d_fs.
  rewrite bytes_le_to_Z_le4, Z_to_bv_unsigned.
  unfold extz. destruct sx; cbv beta iota.
  - change (8 * N.of_nat 4)%N with 32%N.
    unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (Znth i rv) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (Znth i rv) (2 ^ 32)) by lia.
    rewrite swrap32_small by lia. reflexivity.
  - unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
    rewrite (Z.mod_small (Znth i rv) (2 ^ 64)) by lia.
    rewrite (Z.mod_small (Znth i rv) (2 ^ 32)) by lia. reflexivity.
Qed.

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

  Lemma x2_skdeA : forall m1 (dt : list Z) (w minW len st s sv d1 d3 d4 d5 : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa2 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 ->
    (forall m2 xb0 xb2 xb7 x28', 0 < RVC (tl + 1 - w) minW ->
       STD m2 w minW len st s sv d1 d3 d4 d5 (RVC (tl + 1 - w) minW) 0 dt xb0 xb2 xb7 (Z_to_bv 64 WK) x28') ->
    (forall m2 ya0 ya2, RVC (tl + 1 - w) minW = 0 ->
       STJ m2 w minW len st s sv (Z_to_bv 64 (RVC (tl + 1 - w) minW)) dt xra x5 x6 x7 ya0 (Z_to_bv 64 d1) ya2 (Z_to_bv 64 d3) (Z_to_bv 64 d4) (Z_to_bv 64 d5) xa6 xa7 xs6 (Z_to_bv 64 (4 * st)) xs10 xs11 x28 x29 x30 x31) ->
    STKD m1 w minW len st s sv d1 d3 d4 d5 v344 dt xra x5 x6 x7 xa0 xa2 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HLE HLEN HMIN M2 ST0 ST1 SV KD KJ I.
    open_xbb I. pose proof HY as HY'. open_hx2b HY'.
    pose proof (AF_huf_x2t_bl2i.x2_unp_wkM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UW m1 MU) as UWK1.
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (_ & G2 & G3 & G4 & G5 & G6 & G7).
    clear DTWK DFD DFW HMIN.
    change (WK + wksz <= lo \/ SPV <= WK) with (X2EHide (WK + wksz <= lo \/ SPV <= WK)) in SWS.
    change (DT + 4 * (1 + 2 ^ mtl) <= lo \/ SPV <= DT) with (X2EHide (DT + 4 * (1 + 2 ^ mtl) <= lo \/ SPV <= DT)) in SDS.
    pose proof STATS as (TLR & _).
    destruct (TTB_range tl mtl ltac:(clear - TLR TLM; lia) ltac:(clear - MTL; lia)) as (TTR & _).
    assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; clear - MTL; lia).
    assert (P3 : 2 ^ (mtl - 1) <= 2 ^ 11) by (apply Z.pow_le_mono_r; clear - MTL; lia).
    assert (RVE : Znth (13 * (tl + 1 - w) + minW) rv = RVC (tl + 1 - w) minW) by (apply (proj2 RVXX); clear - HW HLE G3; lia).
    pose proof (proj1 RV) as RVB.
    assert (LRVm : Z.of_nat (length (u32s (map (Z_to_bv 64) rv))) = 624) by (rewrite u32s_length, length_map; clear - RVLEN; lia).
    assert (RSW2 : rng RNG (shad WK) ((WK + wksz + 7) / 8 - WK / 8))
      by (eapply rng_sub; [exact RSW | clear - WKL; lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; clear - WKL WR; Z.div_mod_to_equations; lia]).
    clear RSW RSDT.
    assert (RSPA : rng RNG SPA 408) by (eapply rng_sub; [exact RSTK | clear - LOS SPAB; lia | clear - LOS SPAB; lia]).
    pose proof ABW as ABWu. unfold ablk, AIMG_HI, KLS in ABWu.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    unfold KHIGH in KLO.
    change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2EHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2EHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2EHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (u8arr bsegs m1 (WK + 736) syb) with (X2EHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
    change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2EHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2EHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
    pose proof (x2k_cell1 bsegs m1 SPA _ 272 _ FR eq_refl) as FS272. change (SPA + Z.of_nat 272) with (SPA + 272) in FS272.
    pose proof (x2k_cell1 bsegs m1 SPA _ 360 _ FR eq_refl) as FS360. change (SPA + Z.of_nat 360) with (SPA + 360) in FS360.
    pose proof (x2k_cell1 bsegs m1 SPA _ 256 _ FR eq_refl) as FS256. change (SPA + Z.of_nat 256) with (SPA + 256) in FS256.
    pose proof (x2k_cell1 bsegs m1 SPA _ 288 _ FR eq_refl) as FS288. change (SPA + Z.of_nat 288) with (SPA + 288) in FS288.
    pose proof (x2k_cell1 bsegs m1 SPA _ 336 _ FR eq_refl) as FS336. change (SPA + Z.of_nat 336) with (SPA + 336) in FS336.
    pose proof (x2k_cell1 bsegs m1 SPA _ 64 _ FR eq_refl) as FS64. change (SPA + Z.of_nat 64) with (SPA + 64) in FS64.
    pose proof (x2k_cell1 bsegs m1 SPA _ 72 _ FR eq_refl) as FS72. change (SPA + Z.of_nat 72) with (SPA + 72) in FS72.
    pose proof (x2k_cell1 bsegs m1 SPA _ 80 _ FR eq_refl) as FS80. change (SPA + Z.of_nat 80) with (SPA + 80) in FS80.
    pose proof (x2k_cell1 bsegs m1 SPA _ 88 _ FR eq_refl) as FS88. change (SPA + Z.of_nat 88) with (SPA + 88) in FS88.
    pose proof (x2k_cell1 bsegs m1 SPA _ 96 _ FR eq_refl) as FS96. change (SPA + Z.of_nat 96) with (SPA + 96) in FS96.
    pose proof (x2k_cell1 bsegs m1 SPA _ 104 _ FR eq_refl) as FS104. change (SPA + Z.of_nat 104) with (SPA + 104) in FS104.
    pose proof (x2k_cell1 bsegs m1 SPA _ 112 _ FR eq_refl) as FS112. change (SPA + Z.of_nat 112) with (SPA + 112) in FS112.
    pose proof (x2k_cell1 bsegs m1 SPA _ 352 _ FR eq_refl) as FS352. change (SPA + Z.of_nat 352) with (SPA + 352) in FS352.
    pose proof (x2k_cell1 bsegs m1 SPA _ 344 _ FR eq_refl) as FS344. change (SPA + Z.of_nat 344) with (SPA + 344) in FS344.
    let T := type of FR in change T with (X2EHide T) in FR.
    destruct (Z_lt_le_dec 0 (RVC (tl + 1 - w) minW)) as [NZ | Z0].
    - (kx_runFmd [0x82910] 40%nat [false]
        [KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange wksz 2124 (2^32);
         KZRange SPA (KHIGH + 5408) (2^47 - 528); KZAlign SPA 32; KZAlign DT 4; KZAlign WK 4;
         KZRange tl 1 12; KZRange w 1 12; KZRange minW 2 12; KZRange (tl + 1 - w) 0 12; KZRange st 0 4096; KZRange sv 0 255;
         KZWord (SPA + 272) 8 (WK + 52 * (tl + 1 - w) + 4 * minW); KZWord (SPA + 360) 8 (WK + 52 * (tl + 1 - w));
         KZWord (SPA + 256) 8 (4 * minW); KZWord (SPA + 288) 8 minW; KZWord (SPA + 336) 8 (DT + 4);
         KZWord (SPA + 64) 8 (DT + 12); KZWord (SPA + 72) 8 (DT + 27); KZWord (SPA + 80) 8 (DT + 20); KZWord (SPA + 88) 8 (DT + 19);
         KZWord (SPA + 96) 8 (DT + 35); KZWord (SPA + 104) 8 (DT + 28); KZWord (SPA + 112) 8 (DT + 11); KZWord (SPA + 352) 8 WK;
         KZWr (SPA + 344) 8]
        [(WK + 52 * (tl + 1 - w) + 4 * minW, 4)] [(SPA, 408)] [(WK, wksz)]).
      all: try (unfold KHIGH; clear - KLO LOS SPAB SPT DTL DTH WKL WKH WR ST0 SV TLR HW G3 M2; lia).
      all: kx_read_eq 32%nat RVL; rewrite adenot_wa in RVL.
      all: lazymatch type of RVL with _ = rdval _ _ (wa (estart ?E ?a)) _ _ =>
             assert (EAR : estart E a = WK + 4 * (13 * (tl + 1 - w) + minW)) by x2d_es end.
      all: rewrite EAR, (x2d_rdv m1 WK rv (13 * (tl + 1 - w) + minW) _ RVB), RVE in RVL
             by (clear - RVE G6 G2 P3 HLE TTR MTL HMW G3 HW RVLEN; lia).
      all: lazymatch goal with
           | |- accP _ ?E _ =>
             let b := eval unfold E in E in
             lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
               change E with (kE zv xs);
               apply (kx_acc_rng zv xs RNG WK wksz _ _ RW);
               [lia | kx_zsimp zv; clear - HW HLE TTR MTL HMW G3 TLR WKL WKH WR; lia ..]
             end
           | |- _ => idtac end.
      all: lazymatch goal with
           | |- branch_taken _ _ _ = _ =>
             cbn [edenot]; rewrite RVL;
             apply (range_branch_sound BC_GE 0 0 1 2048); [x2d_u | x2d_u | vm_compute; reflexivity]
           | |- _ => idtac end.
      kx_post_regs.
      unfold X2EHide in HWC, RK, RS0, SYC, RV, NBC, SWS, SDS, FR.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
        lazymatch lg with [SE ?a1 _ _] =>
          assert (EA1 : estart E a1 = SPA + 344) by x2d_es;
          assert (MEQ : mem_denot E m1 lg = write_to_mem m1 (wa (SPA + 344)) (le8 (Z_to_bv 64 (RVC (tl + 1 - w) minW))))
            by (rewrite kx_mem_eq; cbn [mem_denot edenot]; rewrite EA1, RVL; reflexivity);
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 DTC) KXLF) as DTC1;
          pose proof (kx_rw_cells_log bsegs E m1 lg _ _ NBC KXLF) as NBC';
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 HWC) KXLF) as HWC1;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RK) KXLF) as RK1;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RS0) KXLF) as RS01;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 SYC) KXLF) as SYC1;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RV) KXLF) as RV1;
          pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 DTC)) as DTC2;
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
          cbn [log_apart log_inside log_wr] in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
          rewrite ?EA1 in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
          rewrite MEQ in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, DTC2, HWC2, RK2, RS02, SYC2, RV2, WKR', STK', MI', MU', WM' |- *
        end
      end.
      change (Z.of_nat 8) with 8 in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU'.
      assert (LHWm : zlen (map (Z_to_bv 8) hw) <= 256) by (rewrite length_map; lia).
      assert (LRKm : Z.of_nat (length (u32s (map (Z_to_bv 64) rank))) <= 52) by (rewrite u32s_length, length_map; lia).
      assert (LRSm : Z.of_nat (length (u32s (map (Z_to_bv 64) rs0))) = 60) by (rewrite u32s_length, length_map; lia).
      assert (LDTm : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; lia).
      specialize (DTC1 ltac:(split; [|exact Logic.I]; clear - SDS LOS SPAB LDTm DTL; lia)).
      specialize (HWC1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LHWm WKL; lia)).
      specialize (RK1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LRKm WKL; lia)).
      specialize (RS01 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LRSm WKL; lia)).
      specialize (SYC1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR SYLEN WKL; lia)).
      specialize (RV1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LRVm WKL; lia)).
      specialize (NBC' ltac:(cbn [cells_size csize Nat.add]; split; [|exact Logic.I]; clear - FC BOT LOS SPAB FFL; lia)).
      specialize (MI' ltac:(split; [|exact Logic.I]; intros j Hj; apply (wr_at_covers bsegs m1 SPA 408 (SPA + 344) 8 (proj2 FR)); lia)).
      specialize (MU' ltac:(split; [|exact Logic.I]; cbn [inside]; right; right; left; clear - SPAB; lia)).
      pose proof (rw_cells_write bsegs m1 SPA _ 344 (C8 v344) (C8 (Z_to_bv 64 (RVC (tl + 1 - w) minW))) FR eq_refl eq_refl Logic.I) as FR'.
      change (Z.of_nat 344) with 344 in FR'. cbn [cbytes cell_upd csize Nat.eqb Nat.sub] in FR'.
      assert (XLM : XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 (RVC (tl + 1 - w) minW)) dt
                      (write_to_mem m1 (wa (SPA + 344)) (le8 (Z_to_bv 64 (RVC (tl + 1 - w) minW))))).
      { eapply XBB_close; [exact (conj DTC1 DTC2) | exact DTLEN | exact DTBY | exact (conj HWC1 HWC2) | exact (conj RK1 RK2)
          | exact (conj RS01 RS02) | exact RS0LEN | exact RS0NN | exact (conj SYC1 SYC2) | exact SYLEN | exact (conj RV1 RV2)
          | exact RVLEN | exact RVNN | exact WKR' | exact NBC' | exact STK' | exact MI' | exact MU' | exact WM' | exact FR']. }
      lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?r10 _ ?r12 _ _ _ _ ?r17 _ _ _ _ _ _ _ _ _ _ ?r28 _ _ _) _ _ _ _ _ _) =>
        pose proof (KD _ r10 r12 r17 r28 NZ XLM) as KD' end.
      lazymatch goal with |- evtF _ _ _ (MS ?R1 _ _ _ _ _ _) =>
        lazymatch type of KD' with evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => replace R1 with R2; [exact KD' |] end end.
      f_equal; first [reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia].
    - (kx_runFmd [0x82abc] 40%nat [true]
        [KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange wksz 2124 (2^32);
         KZRange SPA (KHIGH + 5408) (2^47 - 528); KZAlign SPA 32; KZAlign DT 4; KZAlign WK 4;
         KZRange tl 1 12; KZRange w 1 12; KZRange minW 2 12; KZRange (tl + 1 - w) 0 12; KZRange st 0 4096; KZRange sv 0 255;
         KZWord (SPA + 272) 8 (WK + 52 * (tl + 1 - w) + 4 * minW); KZWord (SPA + 360) 8 (WK + 52 * (tl + 1 - w));
         KZWord (SPA + 256) 8 (4 * minW); KZWord (SPA + 288) 8 minW; KZWord (SPA + 336) 8 (DT + 4);
         KZWord (SPA + 64) 8 (DT + 12); KZWord (SPA + 72) 8 (DT + 27); KZWord (SPA + 80) 8 (DT + 20); KZWord (SPA + 88) 8 (DT + 19);
         KZWord (SPA + 96) 8 (DT + 35); KZWord (SPA + 104) 8 (DT + 28); KZWord (SPA + 112) 8 (DT + 11); KZWord (SPA + 352) 8 WK;
         KZWr (SPA + 344) 8]
        [(WK + 52 * (tl + 1 - w) + 4 * minW, 4)] [(SPA, 408)] [(WK, wksz)]).
      all: try (unfold KHIGH; clear - KLO LOS SPAB SPT DTL DTH WKL WKH WR ST0 SV TLR HW G3 M2; lia).
      all: kx_read_eq 32%nat RVL; rewrite adenot_wa in RVL.
      all: lazymatch type of RVL with _ = rdval _ _ (wa (estart ?E ?a)) _ _ =>
             assert (EAR : estart E a = WK + 4 * (13 * (tl + 1 - w) + minW)) by x2d_es end.
      all: rewrite EAR, (x2d_rdv m1 WK rv (13 * (tl + 1 - w) + minW) _ RVB), RVE in RVL
             by (clear - RVE G6 G2 P3 HLE TTR MTL HMW G3 HW RVLEN; lia).
      all: lazymatch goal with
           | |- accP _ ?E _ =>
             let b := eval unfold E in E in
             lazymatch b with kx_env (map (Z_to_bv 64) ?zv) ?xs =>
               change E with (kE zv xs);
               apply (kx_acc_rng zv xs RNG WK wksz _ _ RW);
               [lia | kx_zsimp zv; clear - HW HLE TTR MTL HMW G3 TLR WKL WKH WR; lia ..]
             end
           | |- _ => idtac end.
      all: lazymatch goal with
           | |- branch_taken _ _ _ = _ =>
             cbn [edenot]; rewrite RVL;
             apply (range_branch_sound BC_GE 0 0 0 0); [x2d_u | x2d_u | vm_compute; reflexivity]
           | |- _ => idtac end.
      kx_post_regs.
      unfold X2EHide in HWC, RK, RS0, SYC, RV, NBC, SWS, SDS, FR.
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
        lazymatch lg with [SE ?a1 _ _] =>
          assert (EA1 : estart E a1 = SPA + 344) by x2d_es;
          assert (MEQ : mem_denot E m1 lg = write_to_mem m1 (wa (SPA + 344)) (le8 (Z_to_bv 64 (RVC (tl + 1 - w) minW))))
            by (rewrite kx_mem_eq; cbn [mem_denot edenot]; rewrite EA1, RVL; reflexivity);
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 DTC) KXLF) as DTC1;
          pose proof (kx_rw_cells_log bsegs E m1 lg _ _ NBC KXLF) as NBC';
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 HWC) KXLF) as HWC1;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RK) KXLF) as RK1;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RS0) KXLF) as RS01;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 SYC) KXLF) as SYC1;
          pose proof (kx_bytes_at_log bsegs E m1 lg _ _ (proj1 RV) KXLF) as RV1;
          pose proof (kx_wr_at_log bsegs E m1 lg _ _ (proj2 DTC)) as DTC2;
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
          cbn [log_apart log_inside log_wr] in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
          rewrite ?EA1 in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
          rewrite MEQ in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, DTC2, HWC2, RK2, RS02, SYC2, RV2, WKR', STK', MI', MU', WM' |- *
        end
      end.
      change (Z.of_nat 8) with 8 in DTC1, NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU'.
      assert (LHWm : zlen (map (Z_to_bv 8) hw) <= 256) by (rewrite length_map; lia).
      assert (LRKm : Z.of_nat (length (u32s (map (Z_to_bv 64) rank))) <= 52) by (rewrite u32s_length, length_map; lia).
      assert (LRSm : Z.of_nat (length (u32s (map (Z_to_bv 64) rs0))) = 60) by (rewrite u32s_length, length_map; lia).
      assert (LDTm : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; lia).
      specialize (DTC1 ltac:(split; [|exact Logic.I]; clear - SDS LOS SPAB LDTm DTL; lia)).
      specialize (HWC1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LHWm WKL; lia)).
      specialize (RK1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LRKm WKL; lia)).
      specialize (RS01 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LRSm WKL; lia)).
      specialize (SYC1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR SYLEN WKL; lia)).
      specialize (RV1 ltac:(split; [|exact Logic.I]; clear - SWS LOS SPAB WR LRVm WKL; lia)).
      specialize (NBC' ltac:(cbn [cells_size csize Nat.add]; split; [|exact Logic.I]; clear - FC BOT LOS SPAB FFL; lia)).
      specialize (MI' ltac:(split; [|exact Logic.I]; intros j Hj; apply (wr_at_covers bsegs m1 SPA 408 (SPA + 344) 8 (proj2 FR)); lia)).
      specialize (MU' ltac:(split; [|exact Logic.I]; cbn [inside]; right; right; left; clear - SPAB; lia)).
      pose proof (rw_cells_write bsegs m1 SPA _ 344 (C8 v344) (C8 (Z_to_bv 64 (RVC (tl + 1 - w) minW))) FR eq_refl eq_refl Logic.I) as FR'.
      change (Z.of_nat 344) with 344 in FR'. cbn [cbytes cell_upd csize Nat.eqb Nat.sub] in FR'.
      assert (XLM : XL w minW len (Z_to_bv 64 st) (Z_to_bv 64 s) (Z_to_bv 64 (RVC (tl + 1 - w) minW)) dt
                      (write_to_mem m1 (wa (SPA + 344)) (le8 (Z_to_bv 64 (RVC (tl + 1 - w) minW))))).
      { eapply XBB_close; [exact (conj DTC1 DTC2) | exact DTLEN | exact DTBY | exact (conj HWC1 HWC2) | exact (conj RK1 RK2)
          | exact (conj RS01 RS02) | exact RS0LEN | exact RS0NN | exact (conj SYC1 SYC2) | exact SYLEN | exact (conj RV1 RV2)
          | exact RVLEN | exact RVNN | exact WKR' | exact NBC' | exact STK' | exact MI' | exact MU' | exact WM' | exact FR']. }
      lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ ?r10 _ ?r12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
        pose proof (KJ _ r10 r12 ltac:(clear - Z0 G6; lia) XLM) as KJ' end.
      lazymatch goal with |- evtF _ _ _ (MS ?R1 _ _ _ _ _ _) =>
        lazymatch type of KJ' with evtF _ _ _ (MS ?R2 _ _ _ _ _ _) => replace R1 with R2; [exact KJ' |] end end.
      f_equal; first [reflexivity | f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia].
  Qed.

  Lemma x2_skA : AF_huf_x2t_bl2i.SKA_T RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r mtl POST hw rank nbs tl k384 k392 maxW rs0 rv syb.
  Proof.
    unfold AF_huf_x2t_bl2i.SKA_T.
    intros until x31; intros HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE KJ.
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    pose proof (AF_huf_x2t_bl2i.x2_mtl RNG SPV SPA lo DT WK wksz FF mtl HY) as MTL.
    assert (P2m : 2 ^ (mtl - 1) <= 2048) by (change 2048 with (2 ^ 11); apply Z.pow_le_mono_r; lia).
    eapply AF_huf_x2t_bk1.x2_sk1A; try eassumption.
    intros d1 d3 d4 d5 ya0 ya2 L8 SKB.
    assert (E3 : 3 <= TT - (tl + 1 - w)).
    { destruct (Z_lt_le_dec (TT - (tl + 1 - w)) 3) as [LT|GE]; [| exact GE]. exfalso.
      destruct (Z_lt_le_dec (TT - (tl + 1 - w)) 0) as [NEG|NN].
      - rewrite HLEN, Z.pow_neg_r in L8 by lia. lia.
      - assert (2 ^ (TT - (tl + 1 - w)) <= 2 ^ 2) by (apply Z.pow_le_mono_r; lia). change (2 ^ 2) with 4 in *. lia. }
    assert (HL8 : len mod 8 = 0).
    { rewrite HLEN. replace (TT - (tl + 1 - w)) with (TT - (tl + 1 - w) - 3 + 3) by lia.
      rewrite Z.pow_add_r by lia. change (2 ^ 3) with 8. apply Z_mod_mult. }
    eapply x2_skdeA; try eassumption.
    - intros m2 xb0 xb2 xb7 x28' HPOS.
      eapply AF_huf_x2t_bk4.x2_skdloopA with (f := Z.to_nat 256); try eassumption.
      all: first [ lia | reflexivity | (rewrite Z.add_0_r; exact PRE) | (intros; eapply KJ; eassumption) ].
    - intros m2 ya0' ya2' HZ. eapply KJ. rewrite HZ, Z.add_0_r. exact PRE.
  Qed.


  End FX.
  End FM.
End X2B.
End CANSEC1.
