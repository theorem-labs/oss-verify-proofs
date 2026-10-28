(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require KXCell.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bpure AF_huf_x2t_bl2i AF_huf_x2t_bex AF_huf_x2t_bk0.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x2k_shz : forall (m : word -> option byte) lo hi A N, unpoisoned m lo hi -> lo <= A -> 0 <= N -> A + N + 8 <= hi ->
  kshz_fact m ASHOFF A N.
Proof.
  intros m lo hi A N (L0 & H64 & U) HA HN HH x Hx.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  destruct (U (x / 8)) as (b & RB & GB); [lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia |].
  unfold wa in RB. rewrite RB. f_equal. apply (gran_ok_full _ _ GB).
  rewrite Z.min_l by (Z.div_mod_to_equations; lia). lia.
Qed.

Lemma x2k_cell1 : forall segs m A cs k v, rw_cells segs m A cs -> cell_at cs k = Some (C8 v) ->
  rw_cells segs m (A + Z.of_nat k) [C8 v].
Proof.
  intros segs m A cs k v H E.
  destruct (cell_at_split cs k (C8 v) (C8 v) E) as (pre & post & -> & <- & _).
  apply (KXCell.kx_rw_cells_app segs) in H. destruct H as [_ H].
  apply (KXCell.kx_rwc_cons segs) in H. exact (proj1 H).
Qed.

Definition x2k_skD (nb sv : Z) : Z := sv * 4294967297 + (nb + 256) * 281474976776192.

Definition x2k_skbb (nb sv : Z) : bool :=
  let D := x2k_skD nb sv in
  let d3 := D mod 2 ^ 64 / 2 ^ (48 mod 64) in let d4 := D mod 2 ^ 64 / 2 ^ (32 mod 64) in
  let d5 := D mod 2 ^ 64 / 2 ^ (16 mod 64) in
  (D mod 256 =? sv) && ((D / 256) mod 256 =? 0) && (d5 mod 256 =? nb) && ((d5 / 256) mod 256 =? 1)
  && (d4 mod 256 =? sv) && ((d4 / 256) mod 256 =? 0) && (d3 mod 256 =? nb) && ((d3 / 256) mod 256 =? 1)
  && (0 <=? D) && (D <? 2 ^ 64) && (0 <=? d3) && (d3 <? 2 ^ 64) && (0 <=? d4) && (d4 <? 2 ^ 64)
  && (0 <=? d5) && (d5 <? 2 ^ 64).

Lemma x2k_skbb_ok : forall nb sv, x2k_skbb nb sv = true ->
  skbytes nb sv (x2k_skD nb sv) (x2k_skD nb sv mod 2 ^ 64 / 2 ^ (48 mod 64))
    (x2k_skD nb sv mod 2 ^ 64 / 2 ^ (32 mod 64)) (x2k_skD nb sv mod 2 ^ 64 / 2 ^ (16 mod 64)).
Proof.
  intros nb sv H. unfold x2k_skbb in H. cbv zeta in H.
  repeat rewrite Bool.andb_true_iff in H.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with
         | Hc : (_ =? _) = true |- _ => apply Z.eqb_eq in Hc
         | Hc : (_ <=? _) = true |- _ => apply Z.leb_le in Hc
         | Hc : (_ <? _) = true |- _ => apply Z.ltb_lt in Hc
         end.
  unfold skbytes. repeat split; assumption.
Qed.

Lemma x2k_skb_all : forallb (fun nb => forallb (fun sv => x2k_skbb nb sv) (map Z.of_nat (seq 0 256))) (map Z.of_nat (seq 0 16)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma x2k_skb : forall nb sv D, 0 <= nb <= 15 -> 0 <= sv <= 255 -> D = x2k_skD nb sv ->
  skbytes nb sv D (D mod 2 ^ 64 / 2 ^ (48 mod 64)) (D mod 2 ^ 64 / 2 ^ (32 mod 64)) (D mod 2 ^ 64 / 2 ^ (16 mod 64)).
Proof.
  intros nb sv D HN HS ->. apply x2k_skbb_ok.
  pose proof x2k_skb_all as A. rewrite forallb_forall in A.
  specialize (A nb ltac:(apply in_map_iff; exists (Z.to_nat nb); split; [lia | apply in_seq; lia])).
  rewrite forallb_forall in A. apply A. apply in_map_iff. exists (Z.to_nat sv). split; [lia | apply in_seq; lia].
Qed.

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

  Definition x2k_sk1_T (P : Z -> Prop) : Prop :=
    forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31,
    P len ->
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT st dt ->
    (forall (d1 d3 d4 d5 : Z) ya0 ya2, 8 <= len -> skbytes (tl + 1 - w) sv d1 d3 d4 d5 ->
       STKD m1 w minW len st s sv d1 d3 d4 d5 v344 dt xra x5 x6 x7 ya0 ya2 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31) ->
    (forall m2 (dt' : list Z) (v344' : word) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (st + RVC (tl + 1 - w) minW) dt' ->
       STJ m2 w minW len st s sv v344' dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    STSK m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31.

  Lemma x2_sk1A_4 : x2k_sk1_T (fun len => len = 4).
  Proof.
    unfold x2k_sk1_T.
    intros until x31; intros PL HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I.
    cbv beta in PL.
    open_xbb I. pose proof HY as HY'. open_hx2b HY'.
    assert (UDT1 : unpoisoned m1 DT (DT + 4 * (1 + 2 ^ mtl))) by (eapply AF_huf_x2t_bl2i.x2_unp_dtM; eassumption).
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply AF_huf_x2t_bl2i.x2_unp_wkM; eassumption).
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof KLO as KLOu. unfold KHIGH in KLOu.
    assert (RSDT2 : rng RNG (shad DT) ((DT + 4 * (1 + 2 ^ mtl) + 7) / 8 - DT / 8))
      by (eapply rng_sub; [exact RSDT | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSDT.
    assert (RSW2 : rng RNG (shad WK) ((WK + wksz + 7) / 8 - WK / 8))
      by (eapply rng_sub; [exact RSW | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSW.
    pose proof ABD as ABDu. unfold ablk, AIMG_HI, KLS in ABDu.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (x2k_shz m1 WK (WK + wksz) WK 1248 UW1 ltac:(lia) ltac:(lia) ltac:(lia)) as SHZ.
    unfold ASHOFF in SHZ.
    assert (RSW3 : rng RNG (shad WK) (Z.shiftr (1248 + WK mod 8 + 7) 3))
      by (eapply rng_sub; [exact RSW2 | lia | rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    unfold shad, ASHOFF in RSW3.
    pose proof (x2k_cell1 bsegs m1 SPA _ 256 _ FR eq_refl) as F256. change (SPA + Z.of_nat 256) with (SPA + 256) in F256.
    pose proof (x2k_cell1 bsegs m1 SPA _ 376 _ FR eq_refl) as F376. change (SPA + Z.of_nat 376) with (SPA + 376) in F376.
    pose proof (x2k_cell1 bsegs m1 SPA _ 272 _ FR eq_refl) as F272. change (SPA + Z.of_nat 272) with (SPA + 272) in F272.
    pose proof (x2k_cell1 bsegs m1 SPA _ 248 _ FR eq_refl) as F248. change (SPA + Z.of_nat 248) with (SPA + 248) in F248.
    pose proof (x2k_cell1 bsegs m1 SPA _ 312 _ FR eq_refl) as F312. change (SPA + Z.of_nat 312) with (SPA + 312) in F312.
    let T := type of FR in change T with (X2KHide T) in FR.
    change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2KHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2KHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2KHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (u8arr bsegs m1 (WK + 736) syb) with (X2KHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
    change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2KHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2KHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
    assert (STX : 0 <= 2 ^ mtl - st - len <= 4096) by lia.
    repeat match goal with H : ?A \/ ?B |- _ => change (X2KHide (A \/ B)) in H end.
    try unfold X2KHide in SDS. try unfold X2KHide in ABDu.
    rename PL into L4.
    (x2k_hide SDS; x2k_hide ABDu; x2k_hide G1; x2k_hide G2; x2k_hide G5; x2k_hide G6; x2k_hide G7; x2k_hide HLE; x2k_hide HLEN;
        x2k_hide HMIN; x2k_hide HS; x2k_hide ATR; x2k_hide FC; x2k_hide FFL; x2k_hide F64; x2k_hide SP16; x2k_hide SPA32; x2k_hide BOT).
    (let c := eval unfold ASHOFF in ASHOFF in
       let S0 := constr:([0x82818; 0x828d4; 0x82abc] : list Z) in let K0 := constr:([KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange SPA (KHIGH + 5408) (2^47 - 528);
        KZRange sv 0 255; KZRange st 0 4092; KZRange (2 ^ mtl - st - len) 0 4096; KZRange len 4 4;
        KZRange tl 1 12; KZRange w 1 12; KZRange minW 2 12; KZRange (tl + 1 - w) 1 12; KZAlign DT 4; KZAlign WK 4;
        KZShZ c WK 1248; KZWord (SPA + 256) 8 (4 * minW); KZWord (SPA + 376) 8 (18446744073709551615 - (WK + 52 * (tl + 1 - w))); KZWord (SPA + 272) 8 (WK + 52 * (tl + 1 - w) + 4 * minW); KZWord (SPA + 248) 8 (65536 * (tl + 1 - w) + 16777216); KZWord (SPA + 312) 8 len] : list kz) in
       let R0 := constr:([] : list (Z * Z)) in let W0 := constr:([(SPA, 408)] : list (Z * Z)) in let U0 := constr:([(DT, 4 * (1 + 2 ^ mtl))] : list (Z * Z)) in
       kx_prepFm S0 80%nat K0 R0 W0 U0; let D := eval vm_compute in (repeat false 4096) in kx_goFm D).
    all: try (unfold KHIGH; lia).
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => idtac end; x2k_fl).
    (kx_post_regs; cbn [mem_denot];
        lazymatch goal with |- context [Z_to_bv 64 (- WK + ?c)] =>
          replace (Z_to_bv 64 (- WK + c)) with (Z_to_bv 64 (18446744073709551615 - (WK + 676)))
            by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; clear - WKL WKH; Z.div_mod_to_equations; lia) end;
        replace (Z_to_bv 64 (DT + 4 * st + 4)) with (Z_to_bv 64 (DT + 4 + 4 * st)) by (f_equal; lia);
        let L4b := fresh "L4b" in assert (L4b : Z_to_bv 64 len = Z_to_bv 64 4) by (rewrite L4; reflexivity);
        rewrite <- L4b at 2;
        let NB := fresh "NB" in assert (NB : 1 <= tl + 1 - w <= 12) by lia;
        eapply AF_huf_x2t_bk0.x2_sk4A with (m1 := m1) (dt := dt) (w := w) (minW := minW) (len := len) (st := st) (s := s) (sv := sv)
          (k384 := k384) (k392 := k392) (rs0 := rs0) (syb := syb) (rv := rv) (lo := lo) (wksz := wksz) (FF := FF) (mtl := mtl) (m5 := m5)
          (r := r) (hdw := hdw) (v344 := v344);
        first [ assumption
          | lazymatch goal with |- skbytes _ _ _ _ _ _ => eapply x2k_skb; [lia | lia | unfold x2k_skD; lia] end
          | eassumption ]).
  Qed.

  Lemma x2_sk1A_8 : x2k_sk1_T (fun len => 8 <= len).
  Proof.
    unfold x2k_sk1_T.
    intros until x31; intros PL HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I.
    cbv beta in PL.
    open_xbb I. pose proof HY as HY'. open_hx2b HY'.
    assert (UDT1 : unpoisoned m1 DT (DT + 4 * (1 + 2 ^ mtl))) by (eapply AF_huf_x2t_bl2i.x2_unp_dtM; eassumption).
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply AF_huf_x2t_bl2i.x2_unp_wkM; eassumption).
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof KLO as KLOu. unfold KHIGH in KLOu.
    assert (RSDT2 : rng RNG (shad DT) ((DT + 4 * (1 + 2 ^ mtl) + 7) / 8 - DT / 8))
      by (eapply rng_sub; [exact RSDT | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSDT.
    assert (RSW2 : rng RNG (shad WK) ((WK + wksz + 7) / 8 - WK / 8))
      by (eapply rng_sub; [exact RSW | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSW.
    pose proof ABD as ABDu. unfold ablk, AIMG_HI, KLS in ABDu.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (x2k_shz m1 WK (WK + wksz) WK 1248 UW1 ltac:(lia) ltac:(lia) ltac:(lia)) as SHZ.
    unfold ASHOFF in SHZ.
    assert (RSW3 : rng RNG (shad WK) (Z.shiftr (1248 + WK mod 8 + 7) 3))
      by (eapply rng_sub; [exact RSW2 | lia | rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    unfold shad, ASHOFF in RSW3.
    pose proof (x2k_cell1 bsegs m1 SPA _ 256 _ FR eq_refl) as F256. change (SPA + Z.of_nat 256) with (SPA + 256) in F256.
    pose proof (x2k_cell1 bsegs m1 SPA _ 376 _ FR eq_refl) as F376. change (SPA + Z.of_nat 376) with (SPA + 376) in F376.
    pose proof (x2k_cell1 bsegs m1 SPA _ 272 _ FR eq_refl) as F272. change (SPA + Z.of_nat 272) with (SPA + 272) in F272.
    pose proof (x2k_cell1 bsegs m1 SPA _ 248 _ FR eq_refl) as F248. change (SPA + Z.of_nat 248) with (SPA + 248) in F248.
    pose proof (x2k_cell1 bsegs m1 SPA _ 312 _ FR eq_refl) as F312. change (SPA + Z.of_nat 312) with (SPA + 312) in F312.
    let T := type of FR in change T with (X2KHide T) in FR.
    change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2KHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2KHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2KHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (u8arr bsegs m1 (WK + 736) syb) with (X2KHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
    change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2KHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2KHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
    assert (STX : 0 <= 2 ^ mtl - st - len <= 4096) by lia.
    repeat match goal with H : ?A \/ ?B |- _ => change (X2KHide (A \/ B)) in H end.
    try unfold X2KHide in SDS. try unfold X2KHide in ABDu.
    rename PL into L8.
    (x2k_hide SDS; x2k_hide ABDu; x2k_hide G1; x2k_hide G2; x2k_hide G5; x2k_hide G6; x2k_hide G7; x2k_hide HLE; x2k_hide HLEN;
        x2k_hide HMIN; x2k_hide HS; x2k_hide ATR; x2k_hide FC; x2k_hide FFL; x2k_hide F64; x2k_hide SP16; x2k_hide SPA32; x2k_hide BOT).
    (let c := eval unfold ASHOFF in ASHOFF in
       let S0 := constr:([0x82818; 0x828d4; 0x82abc] : list Z) in let K0 := constr:([KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange SPA (KHIGH + 5408) (2^47 - 528);
        KZRange sv 0 255; KZRange st 0 4092; KZRange (2 ^ mtl - st - len) 0 4096; KZRange len 8 4096;
        KZRange tl 1 12; KZRange w 1 12; KZRange minW 2 12; KZRange (tl + 1 - w) 1 12; KZAlign DT 4; KZAlign WK 4;
        KZShZ c WK 1248; KZWord (SPA + 256) 8 (4 * minW); KZWord (SPA + 376) 8 (18446744073709551615 - (WK + 52 * (tl + 1 - w))); KZWord (SPA + 272) 8 (WK + 52 * (tl + 1 - w) + 4 * minW); KZWord (SPA + 248) 8 (65536 * (tl + 1 - w) + 16777216); KZWord (SPA + 312) 8 len] : list kz) in
       let R0 := constr:([] : list (Z * Z)) in let W0 := constr:([(SPA, 408)] : list (Z * Z)) in let U0 := constr:([(DT, 4 * (1 + 2 ^ mtl))] : list (Z * Z)) in
       kx_prepFm S0 80%nat K0 R0 W0 U0; let D := eval vm_compute in (repeat false 4096) in kx_goFm D).
    all: try (unfold KHIGH; lia).
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => idtac end; x2k_fl).
    (kx_post_regs; cbn [mem_denot];
        lazymatch goal with |- context [Z_to_bv 64 (- WK + ?c)] =>
          replace (Z_to_bv 64 (- WK + c)) with (Z_to_bv 64 (18446744073709551615 - (WK + 676)))
            by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; clear - WKL WKH; Z.div_mod_to_equations; lia) end;
        try replace (Z_to_bv 64 (DT + 4 * st + 4)) with (Z_to_bv 64 (DT + 4 + 4 * st)) by (f_equal; lia);
        eapply K8; [exact L8 | | exact I]; eapply x2k_skb; [lia | lia | unfold x2k_skD; lia]).
  Qed.

  Lemma x2_sk1A_2 : x2k_sk1_T (fun len => len = 2).
  Proof.
    unfold x2k_sk1_T.
    intros until x31; intros PL HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I.
    cbv beta in PL.
    open_xbb I. pose proof HY as HY'. open_hx2b HY'.
    assert (UDT1 : unpoisoned m1 DT (DT + 4 * (1 + 2 ^ mtl))) by (eapply AF_huf_x2t_bl2i.x2_unp_dtM; eassumption).
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply AF_huf_x2t_bl2i.x2_unp_wkM; eassumption).
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (P2 : 2 <= 2 ^ mtl <= 4096) by (split; [change 2 with (2^1) at 1 | change 4096 with (2^12)]; apply Z.pow_le_mono_r; lia).
    pose proof KLO as KLOu. unfold KHIGH in KLOu.
    assert (RSDT2 : rng RNG (shad DT) ((DT + 4 * (1 + 2 ^ mtl) + 7) / 8 - DT / 8))
      by (eapply rng_sub; [exact RSDT | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSDT.
    assert (RSW2 : rng RNG (shad WK) ((WK + wksz + 7) / 8 - WK / 8))
      by (eapply rng_sub; [exact RSW | lia | unfold nshad; rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    clear RSW.
    pose proof ABD as ABDu. unfold ablk, AIMG_HI, KLS in ABDu.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR.
    pose proof (x2k_shz m1 WK (WK + wksz) WK 1248 UW1 ltac:(lia) ltac:(lia) ltac:(lia)) as SHZ.
    unfold ASHOFF in SHZ.
    assert (RSW3 : rng RNG (shad WK) (Z.shiftr (1248 + WK mod 8 + 7) 3))
      by (eapply rng_sub; [exact RSW2 | lia | rewrite Z.shiftr_div_pow2 by lia; change (2^3) with 8; Z.div_mod_to_equations; lia]).
    unfold shad, ASHOFF in RSW3.
    pose proof (x2k_cell1 bsegs m1 SPA _ 256 _ FR eq_refl) as F256. change (SPA + Z.of_nat 256) with (SPA + 256) in F256.
    pose proof (x2k_cell1 bsegs m1 SPA _ 376 _ FR eq_refl) as F376. change (SPA + Z.of_nat 376) with (SPA + 376) in F376.
    pose proof (x2k_cell1 bsegs m1 SPA _ 272 _ FR eq_refl) as F272. change (SPA + Z.of_nat 272) with (SPA + 272) in F272.
    pose proof (x2k_cell1 bsegs m1 SPA _ 248 _ FR eq_refl) as F248. change (SPA + Z.of_nat 248) with (SPA + 248) in F248.
    pose proof (x2k_cell1 bsegs m1 SPA _ 312 _ FR eq_refl) as F312. change (SPA + Z.of_nat 312) with (SPA + 312) in F312.
    let T := type of FR in change T with (X2KHide T) in FR.
    change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2KHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2KHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2KHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (u8arr bsegs m1 (WK + 736) syb) with (X2KHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
    change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2KHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2KHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
    assert (STX : 0 <= 2 ^ mtl - st - len <= 4096) by lia.
    repeat match goal with H : ?A \/ ?B |- _ => change (X2KHide (A \/ B)) in H end.
    try unfold X2KHide in SDS. try unfold X2KHide in ABDu.
    rename PL into L2.
    (x2k_hide SDS; x2k_hide ABDu; x2k_hide G1; x2k_hide G2; x2k_hide G5; x2k_hide G7; x2k_hide HLE; x2k_hide HLEN;
        x2k_hide HMIN; x2k_hide HS; x2k_hide ATR; x2k_hide FC; x2k_hide FFL; x2k_hide F64; x2k_hide SP16; x2k_hide SPA32; x2k_hide BOT;
        assert (STX2 : 0 <= 2 ^ mtl - st - 2 <= 4096) by lia).
    (let c := eval unfold ASHOFF in ASHOFF in
       let S0 := constr:([0x82818; 0x828d4; 0x82abc] : list Z) in let K0 := constr:([KZRange DT 4096 (2^47 - 12); KZRange (2 ^ mtl) 2 4096; KZRange WK 4096 (2^47 - 2124); KZRange SPA (KHIGH + 5408) (2^47 - 528);
        KZRange sv 0 255; KZRange st 0 4094; KZRange (2 ^ mtl - st - 2) 0 4096; KZRange len 2 2;
        KZRange tl 1 12; KZRange w 1 12; KZRange minW 2 12; KZRange (tl + 1 - w) 1 12; KZAlign DT 4; KZAlign WK 4;
        KZShZ c WK 1248; KZWord (SPA + 256) 8 (4 * minW); KZWord (SPA + 376) 8 (18446744073709551615 - (WK + 52 * (tl + 1 - w))); KZWord (SPA + 272) 8 (WK + 52 * (tl + 1 - w) + 4 * minW); KZWord (SPA + 248) 8 (65536 * (tl + 1 - w) + 16777216); KZWord (SPA + 312) 8 len;
        KZWr (DT + 4 + 4 * st) 8] : list kz) in
       let R0 := constr:([(DT + 4 + 4 * st, 8)] : list (Z * Z)) in let W0 := constr:([(DT + 4 + 4 * st, 8); (SPA, 408)] : list (Z * Z)) in let U0 := constr:([(DT, 4 * (1 + 2 ^ mtl))] : list (Z * Z)) in
       kx_prepFm S0 80%nat K0 R0 W0 U0; let D := eval vm_compute in (repeat false 4096) in kx_goFm D).
    all: try (unfold KHIGH; lia).
    all: try (lazymatch goal with |- flat _ _ _ /\ _ => idtac end; x2k_fl).
    kx_post_regs.
    unfold X2KHide in HWC, RK, RS0, SYC, RV, NBC, FR, HLE, HW.
    repeat match goal with H : ?A \/ ?B |- _ => change (X2KHide (A \/ B)) in H end.
    (lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (mem_denot ?E m1 ?lg) _) =>
     lazymatch lg with [SE ?a1 _ ?v1; SE ?a2 _ ?v2; SE ?a3 _ ?v3; SE ?a4 _ ?v4] =>
      assert (EA1 : estart E a1 = DT + 4 * (st + 1) + 6) by x2k_es;
      assert (EA2 : estart E a2 = DT + 4 * (st + 1) + 4) by x2k_es;
      assert (EA3 : estart E a3 = DT + 4 * st + 6) by x2k_es;
      assert (EA4 : estart E a4 = DT + 4 * st + 4) by x2k_es;
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
      rewrite ?EA1, ?EA2, ?EA3, ?EA4 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU';
      cbn [replay] in DTC'; rewrite ?EA1, ?EA2, ?EA3, ?EA4 in DTC';
      revert DTC'; x2e_ez; intro DTC'
     end
    end).
    lazymatch type of DTC' with context [Z_to_bv 64 (?Dx mod 2 ^ 64 / 2 ^ (16 mod 64))] =>
      pose proof (x2k_skb (tl + 1 - w) sv Dx ltac:(lia) ltac:(lia) ltac:(unfold x2k_skD; lia)) as SKB end.
    change (Z.of_nat 2) with 2 in FR', NBC', HWC1, RK1, RS01, SYC1, RV1, MI', MU'.
    assert (LHWm : zlen (map (Z_to_bv 8) hw) <= 256) by (rewrite length_map; lia).
    assert (LRKm : Z.of_nat (length (u32s (map (Z_to_bv 64) rank))) <= 52) by (rewrite u32s_length, length_map; lia).
    assert (LRSm : Z.of_nat (length (u32s (map (Z_to_bv 64) rs0))) = 60) by (rewrite u32s_length, length_map; lia).
    assert (LRVm : Z.of_nat (length (u32s (map (Z_to_bv 64) rv))) = 624) by (rewrite u32s_length, length_map; lia).
    pose proof SDS as SDS'. unfold X2KHide in SDS'.
    specialize (FR' ltac:(cbn [cells_size csize Nat.add length]; repeat split; clear - SDS' ST0 STX2 P2 DTL SPAB LOS SPT; lia)).
    pose proof DFD as DFD'. unfold X2KHide in DFD'.
    specialize (NBC' ltac:(cbn [cells_size csize Nat.add length]; repeat split; clear - DFD' ST0 STX2 P2 DTL FFL F64; lia)).
    pose proof DTWK as DTWK'. unfold X2KHide in DTWK'.
    specialize (HWC1 ltac:(repeat split; clear - DTWK' ST0 STX2 P2 DTL WKL WR LHWm LRKm LRSm LRVm SYLEN; lia)).
    specialize (RK1 ltac:(repeat split; clear - DTWK' ST0 STX2 P2 DTL WKL WR LHWm LRKm LRSm LRVm SYLEN; lia)).
    specialize (RS01 ltac:(repeat split; clear - DTWK' ST0 STX2 P2 DTL WKL WR LHWm LRKm LRSm LRVm SYLEN; lia)).
    specialize (SYC1 ltac:(repeat split; clear - DTWK' ST0 STX2 P2 DTL WKL WR LHWm LRKm LRSm LRVm SYLEN; lia)).
    specialize (RV1 ltac:(repeat split; clear - DTWK' ST0 STX2 P2 DTL WKL WR LHWm LRKm LRSm LRVm SYLEN; lia)).
    pose proof (proj2 (proj2 (proj2 DTC))) as WDT. rewrite length_map in WDT.
    specialize (MI' ltac:(repeat split; try exact Logic.I; intros j Hj;
      lazymatch goal with |- wview _ _ (wa (?b + j)) <> None => replace (b + j) with (DT + (b - DT + j)) by ring; apply WDT; clear - Hj ST0 STX2 P2 DTL DTLEN; lia end)).
    specialize (MU' ltac:(repeat split; try exact Logic.I; cbn [inside]; left; clear - ST0 STX2 P2 DTL DTH; lia)).
    lazymatch type of DTC' with u8arr _ _ _ ?b1 => set (BIG := b1) in DTC' end.
    destruct (x2e_dt_of BIG) as [DTE DTBY']. rewrite <- DTE in DTC'.
    assert (LB1 : zlen (map bv_unsigned BIG) = 4 * (1 + 2 ^ mtl))
      by (unfold BIG; rewrite length_map, !replay1_length, length_map; exact DTLEN).
    assert (NB : 0 <= tl + 1 - w <= TT) by (clear - HLE HW HMW; lia).
    destruct SKB as (S1a & S1b & S5a & S5b & S4a & S4b & S3a & S3b & R1 & R3 & R4 & R5).
    assert (PRE0 : x2pref TT st (map bv_unsigned (map (Z_to_bv 8) dt))) by (rewrite x2k_mm by exact DTBY; exact PRE).
    assert (LD : Z.of_nat (length (map (Z_to_bv 8) dt)) = 4 * (1 + 2 ^ mtl)) by (rewrite length_map; exact DTLEN).
    assert (PRE2 : x2pref TT (st + 2) (map bv_unsigned BIG)) by ((unfold BIG; replace (st + 2) with (st + 1 + 1) by ring; apply x2k_c1_step;
      [clear - ST0; lia | rewrite !replay1_length; clear - LD ST0 STX2 P2; lia | | clear - S5a S5b R5 S3a S3b R3 NB; lia | clear - S5a S5b R5 S3a S3b R3 NB; lia | clear - S5a S5b R5 S3a S3b R3 NB; lia | apply length_wtlb];
      apply x2k_c1_step; [clear - ST0; lia | rewrite ?replay1_length; clear - LD ST0 STX2 P2; lia | exact PRE0 | clear - S5a S5b R5 S3a S3b R3 NB; lia | clear - S5a S5b R5 S3a S3b R3 NB; lia | clear - S5a S5b R5 S3a S3b R3 NB; lia | apply length_wtlb])).
    lazymatch goal with |- context [Z_to_bv 64 (- WK + ?c)] =>
      replace (Z_to_bv 64 (- WK + c)) with (Z_to_bv 64 (18446744073709551615 - (WK + 676)))
        by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; cbn [Z.of_N]; clear - WKL WKH; Z.div_mod_to_equations; lia) end.
    replace (Z_to_bv 64 (DT + 4 * st + 4)) with (Z_to_bv 64 (DT + 4 + 4 * st)) by (f_equal; ring).
    eapply (KJ _ (map bv_unsigned BIG) v344).
    - (eapply x2pref_mono; [exact PRE2 | clear - G6 L2; lia]).
    - eapply XBB_close; [exact DTC' | exact LB1 | exact DTBY' | exact (conj HWC1 HWC2) | exact (conj RK1 RK2) | exact (conj RS01 RS02)
        | exact RS0LEN | exact RS0NN | exact (conj SYC1 SYC2) | exact SYLEN | exact (conj RV1 RV2) | exact RVLEN | exact RVNN
        | exact WKR' | exact NBC' | exact STK' | exact MI' | exact MU' | exact WM' | exact FR'].
  Qed.

  Lemma x2_sk1A : forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT st dt ->
    (forall (d1 d3 d4 d5 : Z) ya0 ya2, 8 <= len -> skbytes (tl + 1 - w) sv d1 d3 d4 d5 ->
       STKD m1 w minW len st s sv d1 d3 d4 d5 v344 dt xra x5 x6 x7 ya0 ya2 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31) ->
    (forall m2 (dt' : list Z) (v344' : word) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (st + RVC (tl + 1 - w) minW) dt' ->
       STJ m2 w minW len st s sv v344' dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    STSK m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I.
    destruct (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (EE : 1 <= TT - (tl + 1 - w)).
    { destruct (Z_le_gt_dec (TT - (tl + 1 - w)) 0) as [Hle|Hgt]; [| lia].
      exfalso. rewrite HLEN in G2. destruct (Z.eq_dec (TT - (tl + 1 - w)) 0) as [E0|E0].
      - rewrite E0 in G2. cbn in G2. lia.
      - rewrite Z.pow_neg_r in G2 by lia. lia. }
    assert (LC : len = 2 \/ len = 4 \/ 8 <= len).
    { destruct (Z.eq_dec (TT - (tl + 1 - w)) 1) as [E1|E1]; [left; rewrite HLEN, E1; reflexivity|].
      destruct (Z.eq_dec (TT - (tl + 1 - w)) 2) as [E2|E2]; [right; left; rewrite HLEN, E2; reflexivity|].
      right; right. rewrite HLEN. change 8 with (2 ^ 3). apply Z.pow_le_mono_r; lia. }
    destruct LC as [L | [L | L]].
    - exact (x2_sk1A_2 m1 dt w minW len st s sv v344 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31 L HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I).
    - exact (x2_sk1A_4 m1 dt w minW len st s sv v344 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31 L HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I).
    - exact (x2_sk1A_8 m1 dt w minW len st s sv v344 xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31 L HW HLE HLEN HMIN M2 HS ST0 ST1 SV PRE K8 KJ I).
  Qed.

  End FX.
  End FM.
End X2B.
End CANSEC1.
