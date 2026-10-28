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
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_huf_x2t_bgeo.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF FseWalkMem.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Local Ltac pcoff := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => let p := eval vm_compute in (n - 0x81e48) in p end.
Local Ltac at_stop stops := let p := pcoff in let b := eval vm_compute in (existsb (Z.eqb p) stops) in
  lazymatch b with true => idtac | false => fail end.
Local Ltac walk stops := repeat (tryif at_stop stops then fail else (zstep)).
Local Ltac is_ifpc := lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.
Local Ltac prune K :=
  try ((exfalso; lia));
  try ((exfalso; rewrite ?Z.shiftl_mul_pow2 in K by lia; lia));
  try ((exfalso; rewrite ?KXS.swrap32_small in K by lia; rewrite ?Z.mod_small in K by lia; lia));
  try ((exfalso; lazymatch type of K with context [bv_unsigned (sxb (Z_to_bv 8 ?c))] =>
                    rewrite (sxb_lit c) in K by lia; cbn in K; lia end)).
Local Ltac go stops :=
  walk stops;
  try (is_ifpc; let K := fresh "K" in bcase K; prune K; go stops).
Definition HideP (P : Prop) : Prop := P.
Local Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (HideP (A \/ B)) in H end.

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
  Lemma x2c_sh0n : forall m lo0 hi a, unpoisoned m lo0 hi -> lo0 <= a -> 8 * (a / 8) + 8 <= hi ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m lo0 hi a U L H. assert (0 <= lo0) by (destruct U; lia). rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (a / 8 + ASHOFF) with (ASHOFF + a / 8) by lia.
    eapply unpoisoned_full_rd; [exact U| rewrite shad_div; pose proof (Z.div_le_mono lo0 a 8 ltac:(lia) L); lia| lia].
  Qed.
  Lemma x2c_sh0k : forall m lo0 hi a k, unpoisoned m lo0 hi -> lo0 <= a -> 8 * (a / 8) + 8 <= hi -> k = ASHOFF ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + k)) 1 = Some [Z_to_bv 8 0].
  Proof. intros m lo0 hi a k U L H ->. apply (x2c_sh0n m lo0 hi a U L H). Qed.
  Lemma x2c_acc_rng : forall lo0 len a n, rng RNG lo0 len -> lo0 <= a < lo0 + len -> a + Z.of_nat n <= lo0 + len -> acc_in RNG (Z_to_bv 64 a, n).
  Proof. intros lo0 len a n [R0 [R1 R2]] H1 H2. unfold acc_in; cbn [fst snd]. rewrite unsigned_lit by lia. apply R2; lia. Qed.
  Local Ltac x2c_side := rewrite ?shad_div, ?nshad_div; unfold ASHOFF; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
    rewrite ?Z.mod_small by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; Z.div_mod_to_equations; lia.
  Local Ltac x2c_shload := lazymatch goal with |- context [ov_read_bytes bsegs ?m (Z_to_bv 64 (Z.shiftr ?a 3 + ?k)) 1%nat] =>
      match goal with U : unpoisoned m ?lo0 ?hi |- _ => rewrite (x2c_sh0k m lo0 hi a k U) by (first [reflexivity | x2c_side]) end end; load_post.
  Local Ltac x2c_acchint := lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (Z.shiftr ?a 3 + ?k), 1%nat) =>
        lazymatch goal with H : rng _ (shad WK) _ |- _ => eapply (x2c_acc_rng _ _ _ _ H); x2c_side end
    | |- acc_in _ (Z_to_bv 64 ?a, ?n) =>
        lazymatch goal with H : rng _ WK wksz |- _ => eapply (x2c_acc_rng _ _ _ _ H); x2c_side end
    end.
  Local Ltac acc_hint ::= x2c_acchint.
  Local Ltac x2c_syn := first [ lazymatch goal with |- ?a = ?a => reflexivity end
                              | lazymatch goal with |- ?a = ?b => first [is_evar a | is_evar b]; reflexivity end ].
  Local Ltac x2c_regeq := lazymatch goal with
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [x2c_syn | f_equal; lia
        | f_equal; rewrite ?(Z.mod_small _ 32) by lia; rewrite ?Z.shiftl_1_l; rewrite ?KXS.swrap32_small by lia; lia
        | f_equal; try (lazymatch goal with |- context [Z.lxor ?x ?c] => change c with (2^64 - 1); rewrite (KXS.lxor_ones64 x) by lia end);
          rewrite ?KXS.swrap32_small by lia; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
          repeat rewrite (Z.mod_small _ (2^32)) by lia; repeat rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia
        | apply Z_to_bv_eqm; Z.div_mod_to_equations; lia ]
    | |- _ => x2c_syn end.
  Local Ltac x2c_cell := first [x2c_syn | lazymatch goal with |- ?C ?a = ?C ?b => refine (f_equal C _); x2c_regeq end].
  Local Ltac x2c_cells := lazymatch goal with
    | |- @cons _ _ _ = @cons _ _ _ => refine (f_equal2 (@cons _) _ _); [x2c_cell | x2c_cells]
    | |- _ => x2c_syn end.
  Local Ltac x2c_frame := lazymatch goal with
    | FR0 : rw_cells ?s ?m ?A ?L0 |- rw_cells ?s ?m ?A ?L1 => replace L1 with L0; [exact FR0| x2c_cells] end.
  Local Ltac x2c_transport := lazymatch goal with MU1 : munch [(SPA, SPA + 408)] ?m0 ?mm, WM1 : wmono bsegs ?m0 ?mm |- _ =>
    tryif constr_eq m0 mm then idtac else transport_after_call bsegs m0 mm MU1 WM1 end.
  Lemma x2c_u8_rd : forall m A (bs : list byte) a, u8arr bsegs m A bs -> A <= a < A + zlen bs ->
    ov_read_bytes bsegs m (Z_to_bv 64 a) 1 = Some [nth (Z.to_nat (a - A)) bs (Z_to_bv 8 0)].
  Proof.
    intros m A bs a H R. eapply u8arr_read; [exact H| apply nth_error_nth'; lia| lia| unfold wa; f_equal; lia].
  Qed.
  Local Ltac x2c_syload := lazymatch goal with |- context [ov_read_bytes bsegs ?m (Z_to_bv 64 ?a) 1%nat] =>
      match goal with
      | H : HideP (u8arr bsegs m (WK + 736) ?l) |- _ => rewrite (x2c_u8_rd m (WK + 736) l a H) by lia
      | H : HideP (u8arr bsegs ?m0 (WK + 736) ?l) |- _ =>
          lazymatch goal with MU : munch ?W m0 m, WM : wmono bsegs m0 m |- _ =>
            let H' := fresh "SYT" in
            assert (H' : u8arr bsegs m (WK + 736) l)
              by (apply (u8arr_transport bsegs W m0 m (WK + 736) _ H MU WM); try (match goal with H0 : HideP (WK + wksz <= _ \/ _) |- _ => unfold HideP in H0 end);
                  cbn [disjoint_from]; simpl_sizes; simpl_arr_sizes; slia);
            rewrite (x2c_u8_rd m (WK + 736) l a H') by lia; clear H' end
      end end; load_post.
  Local Ltac solve_load ::= first [ x2c_shload | x2c_syload | solve_load_base | solve_load_image ].
  Lemma x2c_lx63 : forall z, 0 <= z < 9223372036854775808 -> Z.lxor z 9223372036854775808 = z + 9223372036854775808.
  Proof.
    intros z H. change 9223372036854775808 with (2 ^ 63).
    apply ZBridge.zb_lxor_pow2_small; [change (2 ^ 63) with 9223372036854775808; lia| lia].
  Qed.
  Local Ltac prune2 K := prune K;
    try (lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x82d94) _ _ _ _) =>
         exfalso; match goal with K0 : context [Z.b2z] |- _ =>
         rewrite ?Z.shiftl_mul_pow2 in K0 by lia; try change (2 ^ 2) with 4 in K0;
         rewrite ?x2c_lx63 in K0 by lia; rewrite ?Z.mod_small in K0 by lia;
         repeat rewrite (proj2 (Z.ltb_ge _ _)) in K0 by lia; cbn in K0; first [discriminate K0 | lia] end end).
  Local Ltac go2 stops :=
    walk stops;
    try (is_ifpc; let K := fresh "K" in bcase K; prune2 K; go2 stops).

  Lemma x2_shB : forall m1 (dt : list Z) (w minW len st s : Z) (v320 v328 v344 : word)
      xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> st = RV0 w + len * (s - XS1 w) -> x2pref TT st dt ->
    (forall m2 (sv : Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31, minW = 1 -> 0 <= sv <= 255 -> 0 <= st -> st + len <= 2 ^ mtl ->
       x2pref TT (st + RVC (tl + 1 - w) minW) dt ->
       STJ m2 w minW len st s sv v344 dt yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    (forall m2 (sv : Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys10 ys11 y28 y29 y30 y31, 2 <= minW -> 0 <= sv <= 255 -> 0 <= st -> st + len <= 2 ^ mtl ->
       STSK m2 w minW len st s sv v344 dt yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys10 ys11 y28 y29 y30 y31) ->
    STSH m1 w minW len st s v320 v328 v344 dt xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HLE HLEN HMIN HS HST PRE KJ KSK I. open_xbb I. x2_open.
    pose proof STATS as (TLR & _). pose proof (TT_range TLR) as TTR.
    pose proof (xs1_bounds w ltac:(lia)) as XB0. pose proof (xs1_bounds (w + 1) ltac:(lia)) as XB1.
    destruct (l2x_facts w len minW HW HLE HLEN HMIN) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    destruct (l1_facts w (TT - (tl + 1 - w)) HW eq_refl ltac:(lia)) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    assert (ST0 : 0 <= st) by (subst st; assert (0 <= len * (s - XS1 w)) by (apply Z.mul_nonneg_nonneg; lia); lia).
    assert (ST1 : st + len <= 2 ^ mtl)
      by (subst st; assert (len * (s - XS1 w) + len <= (XS1 (w + 1) - XS1 w) * len)
            by (replace (len * (s - XS1 w) + len) with ((s - XS1 w + 1) * len) by lia; apply Z.mul_le_mono_nonneg_r; lia); lia).
    clear HST.
    pose proof (munch_refl [(SPA, SPA + 408)] m1) as MU1. pose proof (wmono_refl bsegs m1) as WM1.
    hide_disj.
    change (HideP (u8arr bsegs m1 DT (map (Z_to_bv 8) dt))) in DTC. change (HideP (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (HideP (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK. change (HideP (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (HideP (u8arr bsegs m1 (WK + 736) syb)) in SYC. change (HideP (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    go2 [2428; 3188; 3916; 3516].
    all: unfold HideP in DTC, HWC, RK, RS0, SYC, RV, SDSA, SWSA.
    all: x2c_transport.
    all: try kx_mkR_foldF.
    all: repeat match goal with K : context [bv_signed (Z_to_bv 64 ?z)] |- _ => rewrite (signed_small z) in K by lia end.
    all: rewrite ?Z.shiftl_mul_pow2 by lia; try change (2 ^ 2) with 4.
    all: setreg_m 18 (DT + 4 + 4 * st).
    all: lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?b)] =>
           pose proof (bv_unsigned_in_range 8 b) as SVR; change (bv_modulus 8) with 256 in SVR end.
    all: lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x82abc) _ _ _ _) =>
        eapply KJ; [lia | lia | exact ST0 | exact ST1 | replace minW with 1 by lia; rewrite G7, Z.add_0_r; exact PRE
                   | close_xbb; unfold X2BF; x2c_frame]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x827c4) _ _ _ _) =>
        setreg_m 24 (4 * st);
        eapply KSK; [lia | lia | exact ST0 | exact ST1 | close_xbb; unfold X2BF; x2c_frame]
    end.
  Qed.

  Section GLUE.
  Hypothesis SKA : forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) -> 2 <= minW ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT st dt ->
    (forall m2 (dt' : list Z) (v344' : word) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (st + RVC (tl + 1 - w) minW) dt' ->
       STJ m2 w minW len st s sv v344' dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys8 ys10 ys11 y28 y29 y30 y31) ->
    STSK m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 x28 x29 x30 x31.
  Hypothesis JNA : forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT (st + RVC (tl + 1 - w) minW) dt ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (st + len) dt' ->
       STSL m2 w minW len st s v344 dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STJ m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31.
  Hypothesis SLA : forall m1 (dt : list Z) (w minW len st s : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl ->
    (forall y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 < XS1 (w + 1) ->
       STSH m1 w minW len (st + len) (s + 1) (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt xra y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    (forall y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 = XS1 (w + 1) ->
       STLT2 m1 w minW len st s v344 dt xra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STSL m1 w minW len st s v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.

  Lemma x2_jsB : forall m1 (dt : list Z) (w minW len st s sv : Z) (v344 : word)
      xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> 0 <= st -> st + len <= 2 ^ mtl -> 0 <= sv <= 255 -> x2pref TT (st + RVC (tl + 1 - w) minW) dt ->
    (forall m2 (dt' : list Z) yra y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 < XS1 (w + 1) -> x2pref TT (st + len) dt' ->
       STSH m2 w minW len (st + len) (s + 1) (Z_to_bv 64 st) (Z_to_bv 64 s) v344 dt' yra y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    (forall m2 (dt' : list Z) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 = XS1 (w + 1) -> x2pref TT (st + len) dt' ->
       STLT2 m2 w minW len st s v344 dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STJ m1 w minW len st s sv v344 dt xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs8 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HLE HLEN HMIN HS ST0 ST1 SV PRE KN KL.
    eapply JNA; [exact HW| exact HLE| exact HLEN| exact HMIN| exact HS| exact ST0| exact ST1| exact SV| exact PRE|].
    intros until y31; intros PRE2.
    eapply SLA; [exact HW| exact HLE| exact HLEN| exact HMIN| exact HS| exact ST0| exact ST1| |].
    - intros; eapply KN; eassumption.
    - intros; eapply KL; eassumption.
  Qed.

  Lemma x2_symB : forall m1 (dt : list Z) (w minW len st s : Z) (v320 v328 v344 : word)
      xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> st = RV0 w + len * (s - XS1 w) -> x2pref TT st dt ->
    (forall m2 (dt' : list Z) (v344' : word) yra y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 < XS1 (w + 1) -> x2pref TT (st + len) dt' ->
       STSH m2 w minW len (st + len) (s + 1) (Z_to_bv 64 st) (Z_to_bv 64 s) v344' dt' yra y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    (forall m2 (dt' : list Z) (v344' : word) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31, s + 1 = XS1 (w + 1) -> x2pref TT (st + len) dt' ->
       STLT2 m2 w minW len st s v344' dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STSH m1 w minW len st s v320 v328 v344 dt xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.
  Proof.
    intros until x31; intros HW HLE HLEN HMIN HS HST PRE KN KL.
    eapply x2_shB; [exact HW| exact HLE| exact HLEN| exact HMIN| exact HS| exact HST| exact PRE| |].
    - intros until y31; intros M1 SV ST0 ST1 PRE1.
      eapply x2_jsB; [exact HW| exact HLE| exact HLEN| exact HMIN| exact HS| exact ST0| exact ST1| exact SV| exact PRE1| |].
      + intros; eapply KN; eassumption.
      + intros; eapply KL; eassumption.
    - intros until y31; intros M2 SV ST0 ST1.
      eapply SKA; [exact HW| exact HLE| exact HLEN| exact HMIN| exact M2| exact HS| exact ST0| exact ST1| exact SV| exact PRE|].
      intros m3 dt3 v344c; do 20 intro; intros PRE1.
      eapply x2_jsB; [exact HW| exact HLE| exact HLEN| exact HMIN| exact HS| exact ST0| exact ST1| exact SV| exact PRE1| |].
      + intros; eapply KN; eassumption.
      + intros; eapply KL; eassumption.
  Qed.

  Lemma x2_symloopB : forall (f : nat) m1 (dt : list Z) (w minW len st s : Z) (v320 v328 v344 : word)
      xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31,
    1 <= w <= maxW -> tl - maxW + 1 <= TT - (tl + 1 - w) -> len = 2 ^ (TT - (tl + 1 - w)) -> minW = Z.max 1 (tl + 1 - w + (tl + 1 - TT)) ->
    XS1 w <= s < XS1 (w + 1) -> XS1 (w + 1) - s <= Z.of_nat f -> st = RV0 w + len * (s - XS1 w) -> x2pref TT st dt ->
    (forall m2 (dt' : list Z) (st' s' : Z) (v344' : word) yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31,
       x2pref TT (RV0 (w + 1)) dt' ->
       STLT2 m2 w minW len st' s' v344' dt' yra y5 y6 y7 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 y31) ->
    STSH m1 w minW len st s v320 v328 v344 dt xra x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 x31.
  Proof.
    induction f as [|f IH]; intros until x31; intros HW HLE HLEN HMIN HS HF HST PRE KL; [lia|].
    destruct (l2x_facts w len minW HW HLE HLEN HMIN) as (G1 & _).
    eapply x2_symB; [exact HW| exact HLE| exact HLEN| exact HMIN| exact HS| exact HST| exact PRE| |].
    - intros until y31; intros HS1 PRE1.
      eapply IH; [exact HW| exact HLE| exact HLEN| exact HMIN| lia| lia| subst st; lia| exact PRE1| exact KL].
    - intros until y31; intros HS1 PRE1.
      eapply KL. replace (RV0 (w + 1)) with (st + len) by (rewrite G1; subst st; rewrite <- HS1; lia). exact PRE1.
  Qed.

  End GLUE.

  End FX.
  End FM.
End X2B.
End CANSEC1.
