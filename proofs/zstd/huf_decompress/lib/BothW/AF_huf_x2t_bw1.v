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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase AF_huf_x2t_hdefs AF_huf_x2t_bdefs AF_huf_x2t_bpure AF_huf_x2t_bl2i.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF FseWalkMem.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.


Definition X2WHide (P : Prop) : Prop := P.


Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.
Ltac x2wd_pcoff := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => let p := eval vm_compute in (n - 0x81e48) in p end.
Ltac x2wd_at_stop stops := let p := x2wd_pcoff in let b := eval vm_compute in (existsb (Z.eqb p) stops) in
  lazymatch b with true => idtac | false => fail end.
Ltac x2wd_walk stops := repeat (tryif x2wd_at_stop stops then fail else (zstep)).
Ltac x2wd_is_ifpc := lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Ltac x2wd_hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (X2WHide (A \/ B)) in H end.


Lemma x2wd_sgn : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with 18446744073709551616.
  change (2 ^ 63) with 9223372036854775808 in *. rewrite Z.mod_small by lia.
  destruct (Z.ltb_spec0 z 9223372036854775808); lia.
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
  Local Ltac setreg_m r z' :=
    let v := StepF.reg_val r in
    lazymatch v with
    | Z_to_bv 64 z' => idtac
    | Z_to_bv 64 ?z => replace (Z_to_bv 64 z) with (Z_to_bv 64 z') by (first [ f_equal; lia | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ])
    end.
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


  Definition x2_w2rB_stmt : Prop := forall m1 (dt : list Z) (w minW len st s sv w2 : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> minW <= w2 <= maxW ->
    x2pref TT (st + RVC (tl + 1 - w) w2) dt ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 y28 y29 y30 y31,
       w2 + 1 <= maxW -> x2pref TT (st + RVC (tl + 1 - w) (w2 + 1)) dt' ->
       STW2 m2 w minW len st s sv (w2 + 1) v344 dt' yra y5 y6 y7 ya0 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 y28 y29 y30 y31) ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       w2 = maxW -> x2pref TT (st + len) dt' ->
       STSL m2 w minW len st s v344 dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STW2 m1 w minW len st s sv w2 v344 dt xra x5 x6 x7 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 x28 x29 x30 x31.
  Ltac x2wd_regeq := lazymatch goal with
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia
        | f_equal; rewrite ?KXS.swrap32_small by lia; repeat rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia ]
    | |- _ => reflexivity end.
  Ltac x2wd_eqs := f_equal; try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal; x2wd_regeq end).

  Ltac x2wd_ifclosed := lazymatch goal with |- evtF ?s ?R ?Q (MS ?r ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
    tryif (match c with context [?x] => is_var x end) then fail else idtac;
    let v := eval vm_compute in c in
    lazymatch v with
    | true => change (evtF s R Q (MS r F (if c then a else b) fc rv m ro)) with (evtF s R Q (MS r F a fc rv m ro))
    | false => change (evtF s R Q (MS r F (if c then a else b) fc rv m ro)) with (evtF s R Q (MS r F b fc rv m ro))
    end end.
  Lemma x2w_sh0n : forall m lo0 hi a, unpoisoned m lo0 hi -> lo0 <= a -> 8 * (a / 8) + 8 <= hi ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m lo0 hi a U L H. assert (0 <= lo0) by (destruct U; lia). rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (a / 8 + ASHOFF) with (ASHOFF + a / 8) by lia.
    eapply unpoisoned_full_rd; [exact U| rewrite shad_div; pose proof (Z.div_le_mono lo0 a 8 ltac:(lia) L); lia| lia].
  Qed.

  Lemma x2w_acc_rng : forall lo0 len a n, rng RNG lo0 len -> lo0 <= a < lo0 + len -> a + Z.of_nat n <= lo0 + len -> acc_in RNG (Z_to_bv 64 a, n).
  Proof. intros lo0 len a n [R0 [R1 R2]] H1 H2. unfold acc_in; cbn [fst snd]. rewrite unsigned_lit by lia. apply R2; lia. Qed.

  Lemma x2w_u32rd : forall m A l a i, u32arr bsegs m A (map (Z_to_bv 64) l) -> a = A + 4 * i -> 0 <= i < zlen l ->
    ov_read_bytes bsegs m (wa a) 4 = Some (le4 (Z_to_bv 64 (Znth i l))).
  Proof. intros m A l a i H E R. eapply u32arr_read; [exact H| apply nth_error_map_Znth; lia| lia| subst a; reflexivity]. Qed.

  Ltac x2w_side := rewrite ?shad_div, ?nshad_div; unfold ASHOFF; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
    rewrite ?Z.mod_small by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; Z.div_mod_to_equations; lia.
  Lemma x2w_sh0k : forall m lo0 hi a k, k = ASHOFF -> unpoisoned m lo0 hi -> lo0 <= a -> 8 * (a / 8) + 8 <= hi ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + k)) 1 = Some [Z_to_bv 8 0].
  Proof. intros m lo0 hi a k -> U L H. exact (x2w_sh0n m lo0 hi a U L H). Qed.
  Ltac x2w_shload := lazymatch goal with |- context [ov_read_bytes bsegs ?m (Z_to_bv 64 (Z.shiftr ?a 3 + ?k)) 1%nat] =>
      match goal with U : unpoisoned m ?lo0 ?hi |- _ => rewrite (x2w_sh0k m lo0 hi a k ltac:(vm_compute; reflexivity) U) by x2w_side end end; load_post.
  Ltac x2w_acchint := lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (Z.shiftr ?a 3 + ?k), 1%nat) =>
        lazymatch goal with H : rng _ (shad WK) _ |- _ => eapply (x2w_acc_rng _ _ _ _ H); x2w_side end
    | |- acc_in _ (Z_to_bv 64 (SPA + ?o), ?n) =>
        lazymatch goal with H : rng _ lo _ |- _ => eapply (x2w_acc_rng _ _ _ _ H); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia end
    | |- acc_in _ (Z_to_bv 64 ?a, ?n) =>
        lazymatch a with context [WK] => idtac end;
        lazymatch goal with H : rng _ WK wksz |- _ => eapply (x2w_acc_rng _ _ _ _ H); x2w_side end
    end.
  Local Ltac solve_load ::= first [ x2w_shload | solve_load_base | solve_load_image ].
  Local Ltac acc_hint ::= x2w_acchint.
  Lemma x2w_zx32 : forall z, 0 <= z < 2^32 -> zx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
  Proof. intros z H. unfold zx32. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
  Lemma x2w_lxs : forall a, 0 <= a < 9223372036854775808 -> Z.lxor a 9223372036854775808 = a + 9223372036854775808.
  Proof.
    intros a H. change 9223372036854775808 with (2 ^ 63) in *. symmetry. apply Z.add_nocarry_lxor.
    apply Z.bits_inj'; intros n Hn. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec 63 n) as [<-|_]; [| apply andb_false_r]. rewrite andb_true_r.
    rewrite Z.testbit_eqb by lia. rewrite (Z.div_small a (2 ^ 63) H). reflexivity.
  Qed.
  Ltac x2wd_norm := rewrite ?FseRdKit2.sx32_small, ?x2w_zx32 by lia.
  Ltac x2wd_prune K :=
    try (rewrite ?FseRdKit2.sx32_small, ?x2w_zx32 in K by lia; rewrite ?unsigned_lit in K by lia; rewrite ?Z.shiftl_mul_pow2 in K by lia);
    try (exfalso; lia);
    try (exfalso; rewrite ?x2wd_sgn in K by lia; lia);
    try (exfalso; rewrite ?Z.mod_small in K by lia; lia);
    try (exfalso; lazymatch type of K with context [Z.lxor] => idtac end;
         rewrite ?x2w_lxs in K by lia; rewrite ?Z.mod_small in K by lia; revert K;
         repeat match goal with |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b) end; intros K;
         first [ vm_compute in K; discriminate K | lia ]).
  Ltac x2wd_walkN stops := repeat (tryif x2wd_at_stop stops then fail else (zstep; try x2wd_norm)).
  Ltac x2wd_goN stops := x2wd_walkN stops;
    try (x2wd_is_ifpc; first [ x2wd_ifclosed | let K := fresh "K" in bcase K; let p := x2wd_pcoff in lazymatch p with 3916 => x2wd_prune K | _ => idtac end ]; x2wd_goN stops).
  Ltac x2w_lay := lazymatch goal with LAY : X2WHide (_ /\ _) |- _ => clear - LAY; unfold X2WHide in LAY;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try unfold zlen in *; try rewrite ?length_map in *; try rewrite ?map_length in *; lia end.
  Ltac x2w_tr m m' MU WM :=
    let W := lazymatch type of MU with munch ?W _ _ => W end in
    repeat match goal with
    | H : u8arr bsegs m ?A ?xs |- _ => apply (u8arr_transport bsegs W m m' A xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_arr_sizes; x2w_lay ]
    | H : u32arr bsegs m ?A ?xs |- _ => apply (u32arr_transport bsegs W m m' A xs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_arr_sizes; x2w_lay ]
    | H : rw_cells bsegs m ?A ?cs |- _ => apply (rw_cells_transport bsegs W m m' A cs) in H; [ | exact MU | exact WM | cbn [disjoint_from]; simpl_sizes; x2w_lay ]
    | H : stk bsegs m ?l ?h |- _ => apply (stk_transport_disjoint bsegs W m m' l h) in H; [ | exact MU | exact WM | cbn [disjoint_from]; x2w_lay ]
    end.
  Lemma x2_w2rB : x2_w2rB_stmt.
  Proof using HY UDT UW ART0 Hr HM HR TP X2HB STATS NBSR LHW BHW LRK TLM HMW HIGH RSFX RVXX.
    unfold x2_w2rB_stmt.
    intros until x31; intros HW HE HL HMN HS ST0 STL SVR HW2 PRE KN KL I.
    open_xbb I. pose proof HY as HY'. open_hx2b HY'.
    pose proof STATS as (TLR & _).
    unfold KHIGH in KLO.
    pose proof (x2_unp_wkM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UW m1 MU) as UW1.
    pose proof (TTB_range tl mtl ltac:(lia) ltac:(lia)) as TTR.
    pose proof (AF_huf_x2t_bl2i.l2x_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW HW HE HL HMN) as (L2A & L2B & L2C & L2D & L2E & L2F & L2G).
    pose proof (AF_huf_x2t_bl2i.w2_facts RNG SPV SPA lo DT WK wksz FF hdw r mtl HY Hr HR hw rank nbs tl STATS NBSR LHW TLM maxW HMW HIGH w len minW w2 _ HW HE HL HMN HW2 eq_refl) as (W2A & W2B & W2C & W2D & W2E & W2F & W2G & W2H & W2I & W2J).
    pose proof (Z.pow_le_mono_r 2 (mtl - 1) 11 ltac:(lia) ltac:(lia)) as P11. change (2 ^ 11) with 2048 in P11.
    assert (HL1 : ov_read_bytes bsegs m1 (wa (WK + 676 + 4 * w2)) 4 = Some (le4 (Z_to_bv 64 (XS1 w2)))) by (rewrite <- (RSFX w2) by lia; eapply x2w_u32rd; [exact RS0| reflexivity| lia]).
    assert (HL2 : ov_read_bytes bsegs m1 (wa (WK + 676 + 4 * (w2 + 1))) 4 = Some (le4 (Z_to_bv 64 (XS1 (w2 + 1))))) by (rewrite <- (RSFX (w2 + 1)) by lia; eapply x2w_u32rd; [exact RS0| reflexivity| lia]).
    assert (HL3 : ov_read_bytes bsegs m1 (wa (WK + 4 * (13 * (tl + 1 - w) + w2))) 4 = Some (le4 (Z_to_bv 64 (RVC (tl + 1 - w) w2)))) by (rewrite <- (proj2 RVXX (tl + 1 - w) w2) by lia; eapply x2w_u32rd; [exact RV| reflexivity| lia]).
    change (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)) with (X2WHide (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (u32arr bsegs m1 WK (map (Z_to_bv 64) rv)) with (X2WHide (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    change (u8arr bsegs m1 DT (map (Z_to_bv 8) dt)) with (X2WHide (u8arr bsegs m1 DT (map (Z_to_bv 8) dt))) in DTC.
    change (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)) with (X2WHide (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)) with (X2WHide (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (u8arr bsegs m1 (WK + 736) syb) with (X2WHide (u8arr bsegs m1 (WK + 736) syb)) in SYC.
    change (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]) with (X2WHide (rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)])) in NBC.
    x2wd_hide_disj.
    zstep; x2wd_goN [46100; 3916].
    all: rewrite ?Z.shiftl_mul_pow2 by lia; change (2 ^ 2) with 4.
    all: setreg_m 10 (DT + 4 + 4 * (st + RVC (tl + 1 - w) w2));
      setreg_m 11 (WK + 736 + XS1 w2);
      setreg_m 12 (WK + 736 + XS1 w2 + (XS1 (w2 + 1) - XS1 w2));
      setreg_m 13 (2 * tl + 2 - w - w2);
      setreg_m 14 (TTB tl mtl);
      setreg_m 15 sv;
      setreg_m 16 2.
    all: unfold X2WHide in *.
    all: assert (STKa : stk bsegs m1 lo (SPA - 112)) by (apply (proj1 (stk_split bsegs m1 lo (SPA - 112) SPA STK ltac:(lia)))).
    all: assert (STKb : stk bsegs m1 (SPA - 112) SPA) by (apply (proj2 (stk_split bsegs m1 lo (SPA - 112) SPA STK ltac:(lia)))).
    all: pose proof (x2_artM RNG m5 SPV SPA lo DT WK wksz FF mtl HY ART0 m1 MU WM) as ART1.
    all: pose proof (x2_unp_dtM RNG m5 SPV SPA lo DT WK wksz FF mtl HY UDT m1 MU) as UDT1.
    all: assert (USY : ltac:(lazymatch type of UW1 with ?P ?mm _ _ => exact (P mm (WK + 736) (WK + 736 + 256)) end))
           by (pose proof UW1 as U0; hnf in U0 |- *; destruct U0 as (U0a & U0b & U0c); split; [lia | split; [lia |]];
               intros G G1 G2 G3; destruct (U0c G ltac:(lia) ltac:(lia) ltac:(lia)) as (b & Eb & Gb);
               exists b; split; [exact Eb | eapply gran_ok_mono; [exact Gb | lia]]).
    all: assert (HHY : x2hb_hyps RNG SPA DT (WK + 736) mtl)
           by first [ exact (x2_helper_hyps RNG SPV SPA lo DT WK wksz FF mtl HY) | exact (x2_helper_hyps RNG m5 SPV SPA lo DT WK wksz FF mtl HY) ].
    all: assert (NBR : 0 <= 2 * tl + 2 - w - w2 <= TTB tl mtl) by lia.
    all: assert (CNT : st + RVC (tl + 1 - w) w2 + 2 ^ (TTB tl mtl - (2 * tl + 2 - w - w2)) * (XS1 (w2 + 1) - XS1 w2) <= 2 ^ mtl)
           by (replace (TTB tl mtl - (2 * tl + 2 - w - w2)) with (TTB tl mtl - (tl + 1 - w) - (tl + 1 - w2)) by lia; lia).
    all: pose proof X2HB as XH; unfold x2hb_stmt in XH.
    all: try kx_mkR_foldF.
    all: eapply evtF_cut;
      [ eapply (XH RNG) with (SYM := WK + 736) (pos := st + RVC (tl + 1 - w) w2) (bg := XS1 w2) (cnt := XS1 (w2 + 1) - XS1 w2)
            (nb := 2 * tl + 2 - w - w2) (T := TTB tl mtl) (bs := sv) (lvl := 2) (dt := dt) (syb := syb);
        lazymatch goal with
        | |- x2hb_hyps _ _ _ _ _ => exact HHY
        | |- mem_inv _ _ => exact MI
        | |- u8arr _ _ _ _ => exact DTC
        | |- zlen _ = _ => first [ exact DTLEN | exact SYLEN ]
        | |- Forall isbyte _ => exact DTBY
        | |- bytes_at _ _ _ _ => exact (proj1 SYC)
        | |- stk _ _ _ _ => exact STKb
        | |- x2hb_art _ => exact ART1
        | |- _ _ DT _ => exact UDT1
        | |- _ _ (WK + 736) _ => exact USY
        | |- tp = _ => exact TP
        | |- x2pref _ _ _ => exact PRE
        | |- _ \/ _ => right; reflexivity
        | |- _ + 2 ^ _ * _ <= _ => exact CNT
        | |- _ => lia
        end
      | idtac ].
    all: intros ms' PO; unfold x2hb_post in PO;
      destruct PO as (y5 & y6 & y7 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y28 & y29 & y30 & y31 & m2 & dt' & E & MU2 & WM2 & MI2 & DTC2 & DTL2 & DTB2 & XP2 & STK2);
      subst ms'.
    all: assert (XP3 : x2pref TT (st + RVC (tl + 1 - w) (w2 + 1)) dt')
           by (eapply x2pref_mono; [exact XP2 | replace (TT - (2 * tl + 2 - w - w2)) with (TT - (tl + 1 - w) - (tl + 1 - w2)) by lia; lia]).
    all: clear HL1 HL2 HL3 STKb XP2 PRE XH.
    all: clear DTC STK.
    all: pose proof (x2b_dtbB mtl MTL) as (DTBR0 & P2R0).
    all: pose proof (x2_bands RNG SPV SPA lo DT WK wksz FF mtl HY) as (_ & _ & BSP0 & _ & _ & _ & BFL0 & BFF0).
    all: pose proof (conj MTL (conj DTL (conj DTH (conj DT4 (conj WKL (conj WKH (conj WK4 (conj WR (conj KLO (conj BOT (conj LOS (conj SPT (conj SP16
           (conj SPAB (conj SPA32 (conj SDS (conj SWS (conj DTWK (conj F64 (conj FFL (conj FC (conj DTBR0 (conj P2R0 (conj BSP0 (conj BFL0 (conj BFF0
           (conj DFD (conj DFW (conj LHW (conj LRK (conj RS0LEN (conj SYLEN RVLEN)))))))))))))))))))))))))))))))) as LAY0.
    all: lazymatch type of LAY0 with ?T => assert (LAY : X2WHide T) by exact LAY0 end; clear LAY0.
    all: x2w_tr m1 m2 MU2 WM2.
    all: lazymatch type of MU with munch ?WB _ _ => lazymatch type of MU2 with munch ?WC _ _ =>
           assert (SUB : sub_fp WC WB) by (unfold sub_fp; cbn [outside]; intros x Hx; revert Hx; x2w_lay);
           pose proof (munch_trans WB m5 m1 m2 MU (munch_weaken WC WB m1 m2 SUB MU2)) as MU';
           pose proof (wmono_trans bsegs m5 m1 m2 WM WM2) as WM' end end.
    all: clear MU WM MU2 WM2 SUB.
    all: assert (STK' : stk bsegs m2 lo SPA) by (eapply stk_merge; [exact STKa | exact STK2 | lia]).
    all: clear STKa STK2.
    all: try clear MI.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | vm_compute; reflexivity]) end.
    all: x2_reunp.
    all: x2wd_hide_disj.
    all: x2wd_goN [3256; 3200; 3916].
    all: try kx_mkR_foldF.
    all: let p := x2wd_pcoff in
      lazymatch p with
      | 3256 => lazymatch goal with |- evtF _ _ _ ?S => eassert (EQS : _ = S); [| rewrite <- EQS; eapply KN; [lia | exact XP3 | close_xbb]] end
      | 3200 => replace w2 with maxW in XP3 by lia; rewrite L2E in XP3;
                lazymatch goal with |- evtF _ _ _ ?S => eassert (EQS : _ = S); [| rewrite <- EQS; eapply KL; [lia | exact XP3 | close_xbb]] end
      end.
    all: x2wd_eqs.
  Qed.

  End FX.
  End FM.
End X2B.
End CANSEC1.
