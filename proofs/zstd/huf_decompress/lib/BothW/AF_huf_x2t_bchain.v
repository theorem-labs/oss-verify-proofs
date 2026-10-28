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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x2t_bgeo.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_huf_x2t_bl2i AF_huf_x2t_bex AF_huf_x2t_bs3 AF_huf_x2t_bw2 AF_huf_x2t_bwl AF_huf_x2t_bk2.
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
  Variables (xs5 xs9 : word).
  Notation ST0 mm xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31 :=
    (ST 0x82068 mm xra x5 x6 x7 xa0 (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 tl) xa4 xa5 xa6 xa7
        xsrc (Z_to_bv 64 hdw) xs5 (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
    (only parsing).

  Notation XBK dt rs0 syb rv mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 (Z_to_bv 64 tl) k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt rs0 syb rv mm) (only parsing).

  Lemma x2_chainB : forall (dt rs0 rv : list Z) (syb : list byte) m1 xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31,
    XBK dt rs0 syb rv m1 ->
    (forall m2 (dt2 rs2 rv2 : list Z) (syb2 : list byte) (q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q136 q144 q152 q160 q192 q208 q224 q232 q240 q248 q256 q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q360 q368 q376 q384 q392 : word) (yra y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 : word),
       XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank q0 q8 q16 q24 q32 q40 q48 q56 q64 q72 q80 q88 q96 q104 q112 q120 q136 q144 q152 q160 q192 q208 q224 q232 q240 q248 q256 q264 q272 q280 q288 q296 q304 q312 q320 q328 q336 q344 q360 q368 q376 q384 q392 dt2 rs2 syb2 rv2 m2 ->
       x2pref TT (2 ^ TT) dt2 -> Znth 0 dt2 = mtl -> Znth 1 dt2 = 1 -> Znth 2 dt2 = TT -> Znth 3 dt2 = hdw / 16777216 ->
       evtF bsegs RNG POST (MS (mkR yra (Z_to_bv 64 SPA) gp tp y5 y6 y7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) (Z_to_bv 64 r) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                              F (Z_to_bv 64 (X2B_ENTRY + 3732)) fc None m2 (seg_rom bsegs))) ->
    evtF bsegs RNG POST (ST0 m1 xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31).
  Proof using HY UDT UW ART0 Hr HM HR TP X2HB STATS NBSR LHW BHW LRK TLM.
    intros dt rs0 rv syb m1 xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31 I0 KEND.
    pose proof STATS as (TLR & _).
    pose proof HY as HY0. open_hx2b HY0.
    pose proof (TTB_range tl mtl ltac:(lia) ltac:(lia)) as TTR.
    eapply AF_huf_x2t_bs3.x2_rsortB; [eassumption .. | exact I0 |].
    intros m2 maxW rs1 rv1 syb1 yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 HMW HIGH RSF1 RVX1 I2.
    pose proof (AF_huf_x2t_bw2.x2_slB RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r mtl HY UDT UW ART0 Hr HM HR TP X2HB POST
                  hw rank nbs tl STATS NBSR LHW BHW LRK TLM k384 k392 maxW HMW HIGH rs1 rv1 syb1 RSF1 RVX1) as SL1.
    assert (SK1 : AF_huf_x2t_bl2i.SKA_T RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r mtl POST hw rank nbs tl k384 k392 maxW rs1 rv1 syb1)
      by (eapply AF_huf_x2t_bk2.x2_skA; eassumption).
    pose proof (AF_huf_x2t_bw2.x2_jnB RNG gp tp F fc m5 SPV SPA lo DT WK wksz FF hdw r mtl HY UDT UW ART0 Hr HM HR TP X2HB POST
                  hw rank nbs tl STATS NBSR LHW BHW LRK TLM k384 k392 maxW HMW HIGH rs1 rv1 syb1 RSF1 RVX1) as JN1.
    eapply AF_huf_x2t_bwl.x2_fillsB with (r := r) (hdw := hdw) (k384 := k384) (k392 := k392) (maxW := maxW) (rs0 := rs1)
      (rv := rv1) (syb := syb1); [eassumption .. | exact I2 | apply x2pref_0 |].
    intros m3 dt3 y24 y224 y232 y240 y248 y256 y272 y280 y288 y312 y320 y328 y344 y360 y376 zra z5 z6 z7 za1 za2 za3 za4 za5 za6 za7 zs2 zs6 zs8 zs9 zs10 zs11 z28 z29 z30 z31 PRE3 I3.
    eapply (AF_huf_x2t_bex.x2_exitB RNG POST F fc m5 m3 SPV SPA lo DT WK wksz FF mtl nbs mtl (hdw mod 2 ^ 64 / 16777216) TT r hw rank dt3 rs1 rv1 syb1);
      [exact HY | exact UDT | lia | lia | reflexivity | reflexivity | reflexivity | reflexivity | lia
      | rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia | lia | lia | exact I3 |].
    intros m4 dt4 w11 w12 I4 Z0 Z1 Z2 Z3 ZI.
    eapply KEND; [exact I4 | | exact Z0 | exact Z1 | exact Z2 | ].
    - intros u Hu. unfold c2ok. rewrite !ZI by lia. exact (PRE3 u Hu).
    - rewrite Z3. rewrite Z.mod_small by lia. reflexivity.
  Qed.
End X2B.
End CANSEC1.
