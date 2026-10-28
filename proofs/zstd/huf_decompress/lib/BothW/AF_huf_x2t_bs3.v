(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg
  AF_huf_x2t_bgeo AF_huf_x2t_bdefs AF_huf_x2t_hdefs AF_huf_x2t_bp1 AF_huf_x2t_bp2 AF_huf_x2t_bpure AF_huf_x2t_bs1 AF_huf_x2t_bs2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXSound KXGoF FseWalkMem.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

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
  Variable POST : machine_state -> Prop.

  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 ASHOFF) xs4 xs5 xs6 xs7
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

  Variables (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k224 k232 k240 k248 k256 k264
             k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word).
  Variables (xs5 xs9 : word).

  Notation XBP v16 v8 v336 v136 v0 v368 v144 v120 dt rs0 syb rv mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank v0 v8 v16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 v120 v136 v144 k152 k160 k192
         (Z_to_bv 64 tl) k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 v336 k344 k360 v368 k376 k384 k392 dt rs0 syb rv mm)
    (only parsing).
  Notation B3W := (16777216 * (hdw mod 2 ^ 64 / 16777216)) (only parsing).

  Notation ST0 mm xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31 :=
    (ST 0x82068 mm xra x5 x6 x7 xa0 (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 tl) xa4 xa5 xa6 xa7
        xsrc (Z_to_bv 64 hdw) xs5 (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
    (only parsing).
  Notation STM mm w cnt xra x5 x6 x7 xa1 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST 0x820f4 mm xra x5 x6 x7 (Z_to_bv 64 (WK + 680)) xa1 (Z_to_bv 64 (2^64 - 1 - (WK + 624))) (Z_to_bv 64 13) (Z_to_bv 64 cnt) xa5 xa6 xa7
        (Z_to_bv 64 TT) (Z_to_bv 64 hdw) (Z_to_bv 64 w) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
    (only parsing).

  Notation XBP1 dt rs0 syb rv mm :=
    (XBP (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 B3W) k368 k144 k120 dt rs0 syb rv mm) (only parsing).

  Ltac x2v_prune K :=
    try ((exfalso; lia));
    try ((exfalso; rewrite ?Z.shiftl_mul_pow2 in K by lia; lia));
    try ((exfalso; rewrite ?KXS.swrap32_small in K by lia; rewrite ?Z.mod_small in K by lia; lia));
    try ((exfalso; lazymatch type of K with context [bv_unsigned (sxb (Z_to_bv 8 ?c))] =>
                      rewrite (sxb_lit c) in K by lia; cbn in K; lia end));
    try ((exfalso; unfold zx32 in K; rewrite ?(unsigned_lit nbs) in K by lia; rewrite ?(Z.mod_small nbs) in K by lia;
                    rewrite ?unsigned_lit in K by lia; lia)).
  Ltac x2v_go stops :=
    walk stops;
    try (is_ifpc; let K := fresh "K" in bcase K; x2v_prune K; x2v_go stops).

  Lemma x2v_sh0n : forall m lo0 hi a, unpoisoned m lo0 hi -> lo0 <= a -> 8 * (a / 8) + 8 <= hi ->
    ov_read_bytes bsegs m (Z_to_bv 64 (Z.shiftr a 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m lo0 hi a U L H. assert (0 <= lo0) by (destruct U; lia). rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (a / 8 + ASHOFF) with (ASHOFF + a / 8) by lia.
    eapply unpoisoned_full_rd; [exact U| rewrite shad_div; pose proof (Z.div_le_mono lo0 a 8 ltac:(lia) L); lia| lia].
  Qed.

  Lemma x2v_acc_rng : forall lo0 len a n, rng RNG lo0 len -> lo0 <= a < lo0 + len -> a + Z.of_nat n <= lo0 + len -> acc_in RNG (Z_to_bv 64 a, n).
  Proof. intros lo0 len a n [R0 [R1 R2]] H1 H2. unfold acc_in; cbn [fst snd]. rewrite unsigned_lit by lia. apply R2; lia. Qed.

  Lemma x2v_u32rd : forall m A l a i, u32arr bsegs m A (map (Z_to_bv 64) l) -> a = A + 4 * i -> 0 <= i < zlen l ->
    ov_read_bytes bsegs m (wa a) 4 = Some (le4 (Z_to_bv 64 (Znth i l))).
  Proof. intros m A l a i H E R. eapply u32arr_read; [exact H| apply nth_error_map_Znth; lia| lia| subst a; reflexivity]. Qed.

  Lemma x2v_unp_st4 : forall m a v, unpoisoned m WK (WK + wksz) -> WK <= a -> a + 4 <= WK + wksz ->
    unpoisoned (write_to_mem m (wa a) (le4 v)) WK (WK + wksz).
  Proof.
    intros m a v U H1 H2. open_hx2b HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABW. unfold KHIGH in KLO.
    apply unpoisoned_write_other; [exact U| lia| rewrite length_le4; lia| rewrite length_le4, !shad_div; unfold ASHOFF; Z.div_mod_to_equations; lia].
  Qed.

  Ltac x2v_side := rewrite ?shad_div, ?nshad_div; unfold ASHOFF; rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2 by lia;
    rewrite ?Z.mod_small by (rewrite ?Z.shiftl_mul_pow2 by lia; lia); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; Z.div_mod_to_equations; lia.
  Ltac x2v_shload := lazymatch goal with |- context [ov_read_bytes bsegs ?m (Z_to_bv 64 (Z.shiftr ?a 3 + ASHOFF)) 1%nat] =>
      first [ lazymatch goal with U : unpoisoned m ?lo0 ?hi |- _ => rewrite (x2v_sh0n m lo0 hi a U) by x2v_side end
            | lazymatch m with write_to_mem ?m0 (Z_to_bv 64 ?a0) (le4 ?v0) =>
                lazymatch goal with U : unpoisoned m0 WK (WK + wksz) |- _ =>
                  let U2 := fresh "U" in
                  assert (U2 : unpoisoned m WK (WK + wksz)) by (apply (x2v_unp_st4 m0 a0 v0 U); x2v_side);
                  rewrite (x2v_sh0n m WK (WK + wksz) a U2) by x2v_side end end ] end; load_post.
  Ltac x2v_acchint := lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (Z.shiftr ?a 3 + ASHOFF), 1%nat) =>
        lazymatch goal with H : rng _ (shad WK) _ |- _ => eapply (x2v_acc_rng _ _ _ _ H); x2v_side end
    | |- acc_in _ (Z_to_bv 64 ?a, ?n) =>
        lazymatch goal with H : rng _ WK wksz |- _ => eapply (x2v_acc_rng _ _ _ _ H); x2v_side end
    end.
  Local Ltac solve_load ::= first [ x2v_shload | solve_load_base | solve_load_image ].
  Local Ltac acc_hint ::= x2v_acchint.

  Notation XS1 w := (xs1 rank w).
  Notation RINV w rs0 := (x2w_rinv rank w rs0).

  Ltac x2v_regeq := lazymatch goal with
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia
        | f_equal; try (lazymatch goal with |- context [Z.lxor ?x ?c] => change c with (2^64 - 1); rewrite (KXS.lxor_ones64 x) by lia end);
          rewrite ?KXS.swrap32_small by lia; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
          repeat rewrite (Z.mod_small _ (2^32)) by lia; repeat rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia ]
    | |- _ => reflexivity end.
  Ltac x2v_eqs := f_equal; try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal; x2v_regeq end).

  Notation STRp pc mm maxW w acc xra xa2 xa5 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 (WK + 680 + 4 * w)) (Z_to_bv 64 (4 * (maxW + 1))) (Z_to_bv 64 (4 * w))
       (Z_to_bv 64 (WK + 680)) (Z_to_bv 64 (WK + 680 + 4 * w)) xa2 (Z_to_bv 64 (Z.shiftl (maxW + 1) 32)) (Z_to_bv 64 (tl - maxW)) xa5
       (Z_to_bv 64 (2^64 - 1 - (WK + 680))) (Z_to_bv 64 (maxW + 1))
       (Z_to_bv 64 TT) (Z_to_bv 64 hdw) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32))
       (Z_to_bv 64 acc) x29 x30 x31) (only parsing).
  Notation STR mm maxW w acc xra xa2 xa5 x29 x30 x31 := (STRp 0x8216c mm maxW w acc xra xa2 xa5 x29 x30 x31) (only parsing).
  Notation STR2 mm maxW tot xra xa2 xa5 x30 x31 := (STRp 0x821e0 mm maxW (maxW + 1) tot xra xa2 xa5 (Z_to_bv 64 tot) x30 x31) (only parsing).

  Notation STSp pc mm maxW s xra xa1 xa2 xa5 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 s) (Z_to_bv 64 (2^64 - 1 - (WK + 992))) (Z_to_bv 64 (2^64 - 1 - (WK + 736)))
       (Z_to_bv 64 (WK + 680)) xa1 xa2 (Z_to_bv 64 (Z.shiftl (maxW + 1) 32)) (Z_to_bv 64 (tl - maxW)) xa5
       (Z_to_bv 64 (2^64 - 1 - (WK + 680))) (Z_to_bv 64 nbs)
       (Z_to_bv 64 TT) (Z_to_bv 64 hdw) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32))
       (Z_to_bv 64 256) (Z_to_bv 64 255) x30 x31) (only parsing).
  Notation STS mm maxW s xra xa1 xa2 xa5 x30 x31 := (STSp 0x82238 mm maxW s xra xa1 xa2 xa5 x30 x31) (only parsing).
  Notation STE mm maxW xra xa1 xa2 xa5 x30 x31 := (STSp 0x822d8 mm maxW nbs xra xa1 xa2 xa5 x30 x31) (only parsing).

  Ltac x2s_prune K := x2v_prune K;
    try ((exfalso; rewrite ?KXS.u8_lit in K; rewrite ?Z.shiftl_mul_pow2 in K by lia; Z.div_mod_to_equations; lia));
    try ((exfalso; rewrite ?sx32_small in K by lia; rewrite ?unsigned_lit in K by lia; lia)).
  Ltac x2s_go stops :=
    walk stops;
    try (is_ifpc; let K := fresh "K" in bcase K; x2s_prune K; x2s_go stops).

  Notation XBP2 dt rs0 syb rv mm :=
    (XBP (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 B3W) (Z_to_bv 64 TT)
         (Z_to_bv 64 (2^64 - 1 - WK)) k120 dt rs0 syb rv mm) (only parsing).
  Notation STVp pc mm maxW w acc xra x7 xa1 x28 :=
    (ST pc mm xra (Z_to_bv 64 acc) (Z_to_bv 64 32) x7 (Z_to_bv 64 (WK + 624 + 4 * w)) xa1 (Z_to_bv 64 (TT - tl + maxW))
        (Z_to_bv 64 (Z.shiftl (maxW + 1) 32)) (Z_to_bv 64 (TT - tl - 1 + w)) (Z_to_bv 64 (WK + 624 + 4 * w)) (Z_to_bv 64 (4 * (maxW + 1)))
        (Z_to_bv 64 (4 * w))
        (Z_to_bv 64 TT) (Z_to_bv 64 WK) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (WK + 992)) xs9
        (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32))
        x28 (Z_to_bv 64 255) (Z_to_bv 64 (2^64 - 1 - WK)) (Z_to_bv 64 (tl - maxW + 1))) (only parsing).
  Notation STV mm maxW w xra x7 xa1 x28 := (STVp 0x82324 mm maxW w (rv0 rank tl TT w) xra x7 xa1 x28) (only parsing).
  Notation STW mm maxW xra x7 xa1 x28 := (STVp 0x8239c mm maxW (maxW + 1) (rv0 rank tl TT (maxW + 1)) xra x7 xa1 x28) (only parsing).


  Notation XBW maxW dt rs0 syb rv mm :=
    (XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank (Z_to_bv 64 B3W) (Z_to_bv 64 mtl) (Z_to_bv 64 r) k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112
         (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (2^64 - 1 - WK)) k152 k160 k192 (Z_to_bv 64 tl)
         k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 (Z_to_bv 64 (DT + 4)) k344 k360 (Z_to_bv 64 TT) k376 k384 k392
         dt rs0 syb rv mm) (only parsing).
  Notation STQ mm maxW xra x5 x6 x7 xa0 xa1 xa4 xa5 xa6 xa7 xs2 xs6 xs8 xs9 xs10 xs11 x28 x29 x30 :=
    (ST 0x824b0 mm xra x5 x6 x7 xa0 xa1 (Z_to_bv 64 (TT - tl + maxW)) (Z_to_bv 64 (2^32 * (maxW + 1))) xa4 xa5 xa6 xa7
        xs2 (Z_to_bv 64 WK) (Z_to_bv 64 maxW) xs6 (Z_to_bv 64 (WK + 736)) xs8 xs9 xs10 xs11
        x28 x29 x30 (Z_to_bv 64 (tl - maxW + 1))) (only parsing).
  Notation STIp pc mm maxW c w xra x7 xa0 xa1 x28 :=
    (ST pc mm xra (Z_to_bv 64 (2^64 - 1 - (WK + 52 * c))) (Z_to_bv 64 w) x7 xa0 xa1 (Z_to_bv 64 (TT - tl + maxW))
        (Z_to_bv 64 (Z.shiftl (maxW + 1) 32)) (Z_to_bv 64 12) (Z_to_bv 64 c) (Z_to_bv 64 52) (Z_to_bv 64 (WK + 52 * c))
        (Z_to_bv 64 TT) (Z_to_bv 64 WK) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (WK + 992)) xs9
        (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32))
        x28 (Z_to_bv 64 255) (Z_to_bv 64 (2^64 - 1 - WK)) (Z_to_bv 64 (tl - maxW + 1))) (only parsing).
  Notation STI mm maxW c w xra x7 xa0 xa1 x28 := (STIp 0x823e4 mm maxW c w xra x7 xa0 xa1 x28) (only parsing).

  Lemma x2r_sh : forall w, 0 <= w < 2^31 -> Z.shiftr (Z.shiftl w 32 mod 18446744073709551616) 30 = 4 * w.
  Proof.
    intros w Hw. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (w * 2 ^ 32) with (4 * w * 2 ^ 30) by ring. apply Z.div_mul. lia.
  Qed.
  Lemma x2r_val : forall x c, 0 <= x < 2^31 -> 0 <= c < 32 ->
    bv_swrap 32 (Z.shiftr (bv_wrap 32 x) (c mod 32)) = x / 2 ^ c.
  Proof.
    intros x c Hx Hc. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296.
    rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small c 32) by lia. rewrite Z.shiftr_div_pow2 by lia.
    apply KXS.swrap32_small. split; [apply Z.div_pos; lia|].
    apply (Z.le_lt_trans _ x); [apply Z.div_le_upper_bound; [lia|]; pose proof (Z.pow_pos_nonneg 2 c ltac:(lia) ltac:(lia)); nia | lia].
  Qed.
  Ltac x2r_norm K :=
    try (rewrite x2r_sh in K by lia); try (rewrite KXS.swrap32_small in K by lia); rewrite ?Z.mod_small in K by lia.
  Ltac x2r_prune K := x2r_norm K;
    try (exfalso; lia);
    try (exfalso; lazymatch type of K with context [bv_unsigned (sxb (Z_to_bv 8 ?c))] =>
                    rewrite (sxb_lit c) in K by lia; cbn in K; lia end).
  Ltac x2r_go stops :=
    walk stops;
    try (is_ifpc; let K := fresh "K" in bcase K; x2r_prune K; x2r_go stops).

  Lemma x2r_rows_step : forall maxW c w rv v, 1 <= maxW <= tl -> tl <= 12 -> 1 <= c <= 11 -> 1 <= w <= maxW ->
    AF_huf_x2t_bpure.ROWS rank tl mtl maxW c w rv -> zlen rv = 156 ->
    v = rvc rank tl TT c w ->
    AF_huf_x2t_bpure.ROWS rank tl mtl maxW c (w + 1) (Zupd (13 * c + w) v rv).
  Proof.
    intros maxW c w rv v HMX HTL HC HW (R0 & RC & RWW) RL ->. split; [| split].
    - intros v' Hv. rewrite Znth_Zupd_other by lia. apply R0; lia.
    - intros c' v' Hc Hv. rewrite Znth_Zupd_other by lia. apply RC; lia.
    - intros v' Hv. destruct (Z.eq_dec v' w) as [->|NE].
      + apply Znth_Zupd_same. unfold FseNCount.Zlength. lia.
      + rewrite Znth_Zupd_other by lia. apply RWW; lia.
  Qed.

  Lemma x2_w_entryB : forall m1 (dt rs0 rv : list Z) (syb : list byte) (maxW : Z) xra x7 xa1 x28,
    XBP2 dt rs0 syb rv m1 -> 1 <= maxW <= tl ->
    (forall m2 (y7 ya0 ya1 y28 : word), tl - maxW + 1 <= TT - (tl + 1 - maxW) -> XBW maxW dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STI m2 maxW (tl - maxW + 1) 1 xra y7 ya0 ya1 y28)) ->
    (forall m2 yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30,
       TT - (tl + 1 - maxW) < tl - maxW + 1 -> XBW maxW dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STQ m2 maxW yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30)) ->
    evtF bsegs RNG POST (STW m1 maxW xra x7 xa1 x28).
  Proof.
    intros until x28; intros I HMW KI KQ. pose proof STATS as (TLR & _).
    open_xbb I. open_hx2b HY. pose proof (TTB_range tl mtl ltac:(lia) ltac:(lia)) as TTR. hide_disj.
    pose proof (munch_refl [(SPA, SPA + 408)] m1) as MU1. pose proof (wmono_refl bsegs m1) as WM1.
    change (HideP (u8arr bsegs m1 DT (map (Z_to_bv 8) dt))) in DTC. change (HideP (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (HideP (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK.
    change (HideP (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (HideP (u8arr bsegs m1 (WK + 736) syb)) in SYC. change (HideP (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    zstep; x2r_go [1436; 1640; 3916].
    all: unfold HideP in *.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call bsegs m1 mm MU1 WM1 end.
    all: try kx_mkR_foldF.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x823e4) _ _ _ _) =>
             match goal with |- evtF _ _ _ ?s0 => eassert (EQS : _ = s0); [| rewrite <- EQS; eapply KI; [lia| close_xbb]] end
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x824b0) _ _ _ _) =>
             match goal with |- evtF _ _ _ ?s0 => eassert (EQS : _ = s0); [| rewrite <- EQS; eapply KQ; [lia| close_xbb]] end
         end.
    all: x2v_eqs.
  Qed.

  Lemma x2_wi_bodyB : forall m1 (dt rs0 rv : list Z) (syb : list byte) (maxW c w : Z) xra x7 xa0 xa1 x28,
    XBW maxW dt rs0 syb rv m1 -> 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) ->
    tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> 1 <= w <= maxW -> AF_huf_x2t_bpure.ROWS rank tl mtl maxW c w rv ->
    (forall m2 (rv' : list Z) (y7 ya0 ya1 y28 : word), w + 1 <= maxW -> XBW maxW dt rs0 syb rv' m2 ->
       AF_huf_x2t_bpure.ROWS rank tl mtl maxW c (w + 1) rv' ->
       evtF bsegs RNG POST (STI m2 maxW c (w + 1) xra y7 ya0 ya1 y28)) ->
    (forall m2 (rv' : list Z) (y7 ya0 ya1 y28 : word), w = maxW -> c + 1 <= TT - (tl + 1 - maxW) -> XBW maxW dt rs0 syb rv' m2 ->
       AF_huf_x2t_bpure.ROWS rank tl mtl maxW (c + 1) 1 rv' ->
       evtF bsegs RNG POST (STI m2 maxW (c + 1) 1 xra y7 ya0 ya1 y28)) ->
    (forall m2 (rv' : list Z) yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30,
       w = maxW -> c = TT - (tl + 1 - maxW) -> XBW maxW dt rs0 syb rv' m2 ->
       AF_huf_x2t_bpure.ROWS rank tl mtl maxW (c + 1) 1 rv' ->
       evtF bsegs RNG POST (STQ m2 maxW yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30)) ->
    evtF bsegs RNG POST (STI m1 maxW c w xra x7 xa0 xa1 x28).
  Proof.
    intros until x28; intros I HMW HIGH HC HW RRW KN KR KX. pose proof STATS as (TLR & _).
    assert (MTL12 : mtl <= 12) by (open_hx2b HY; lia).
    pose proof (TTB_range tl mtl ltac:(lia) ltac:(lia)) as TTR.
    pose proof (x2b_dtbB mtl ltac:(lia)) as DTBR.
    assert (VW : Znth w rv = rv0 rank tl TT w) by (destruct RRW as (R0 & _); apply R0; lia).
    assert (RB0 : 0 <= rv0 rank tl TT w <= 2 ^ mtl)
      by (eapply (rv0_bounds hw rank nbs tl mtl STATS TLM ltac:(lia) maxW HMW HIGH w); lia).
    assert (RCX : 0 <= rvc rank tl TT c w <= rv0 rank tl TT w /\ rvc rank tl TT c w = rv0 rank tl TT w / 2 ^ c)
      by (eapply rvc_val; eauto; lia).
    destruct RCX as (RC0 & _).
    assert (RVL : zlen rv = 156) by (open_xbb I; exact RVLEN).
    assert (RRW2 : AF_huf_x2t_bpure.ROWS rank tl mtl maxW c (w + 1) (Zupd (13 * c + w) (rvc rank tl TT c w) rv))
      by (eapply x2r_rows_step; [lia| lia| lia| lia| exact RRW| exact RVL| reflexivity]).
    assert (I2 : XBW maxW dt rs0 syb (Zupd (13 * c + w) (rvc rank tl TT c w) rv)
                   (write_to_mem m1 (Z_to_bv 64 (WK + 52 * c + Z.shiftl (w mod 4294967296) 2)) (le4 (Z_to_bv 64 (rvc rank tl TT c w))))).
    { replace (Z_to_bv 64 (WK + 52 * c + Z.shiftl (w mod 4294967296) 2)) with (wa (WK + 4 * (13 * c + w)))
        by (unfold wa; f_equal; rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia).
      eapply x2s_xbb_rv; eauto; lia. }
    open_xbb I. open_hx2b HY. hide_disj.
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x2w_unp_wk; eauto).
    pose proof (x2v_u32rd m1 WK rv (WK + Z.shiftl (w mod 4294967296) 2) w RV
                  ltac:(rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia) ltac:(lia)) as HRV.
    assert (HS : store_ok bsegs m1 (wa (WK + 52 * c + Z.shiftl (w mod 4294967296) 2)) 4 = true)
      by (eapply (u32arr_store_ok bsegs m1 WK (map (Z_to_bv 64) rv) (13 * c + w)); [exact RV| rewrite length_map; lia|
          f_equal; rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; lia]).
    hide_cells.
    zstep; x2r_go [1504; 1640; 3916].
    rewrite VW. rewrite (sx32_small (rv0 rank tl TT w)) by lia.
    x2r_go [1512; 1640; 3916].
    rewrite (x2r_val (rv0 rank tl TT w) c) by lia. change (rv0 rank tl TT w / 2 ^ c) with (rvc rank tl TT c w).
    zstep.
    unfold HideP in *.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (WK + 52 * c + Z.shiftl (w mod 4294967296) 2)) (le4 (Z_to_bv 64 (rvc rank tl TT c w)))) in *.
    clearbody m2.
    clear DTC DTLEN DTBY HWC RK RS0 RS0LEN RS0NN SYC SYLEN RV RVLEN RVNN WKR NBC STK MI MU WM FR HS UW1 HRV.
    open_xbb I2. hide_disj.
    assert (UW2 : unpoisoned m2 WK (WK + wksz)) by (eapply x2w_unp_wk; eauto).
    x2r_go [1436; 1640; 3916]; unfold HideP in *; try kx_mkR_foldF;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x823e4) _ _ _ _) =>
        first
          [ assert (HN : w + 1 <= maxW) by lia;
            match goal with |- evtF _ _ _ ?s0 => eassert (EQS : _ = s0); [| rewrite <- EQS; eapply KN; [exact HN| exact I2| exact RRW2]] end
          | assert (EW : w = maxW) by lia; subst w;
            match goal with |- evtF _ _ _ ?s0 =>
              eassert (EQS : _ = s0); [| rewrite <- EQS; eapply KR; [reflexivity| lia| exact I2| eapply (rows_next hw); exact RRW2]] end ]
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x824b0) _ _ _ _) =>
        assert (EW : w = maxW) by lia; subst w;
        match goal with |- evtF _ _ _ ?s0 =>
          eassert (EQS : _ = s0); [| rewrite <- EQS; eapply KX; [reflexivity| lia| exact I2| eapply (rows_next hw); exact RRW2]] end
    end.
    all: x2v_eqs.
  Qed.

  Lemma x2_wi_loopB : forall (f : nat) m1 (dt rs0 rv : list Z) (syb : list byte) (maxW c w : Z) xra x7 xa0 xa1 x28,
    XBW maxW dt rs0 syb rv m1 -> 1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) ->
    tl + 1 - maxW <= c <= TT - (tl + 1 - maxW) -> 1 <= w <= maxW ->
    13 * (TT - (tl + 1 - maxW) - c) + (maxW + 1 - w) <= Z.of_nat f -> AF_huf_x2t_bpure.ROWS rank tl mtl maxW c w rv ->
    (forall m2 (rv' : list Z) yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30,
       XBW maxW dt rs0 syb rv' m2 -> AF_huf_x2t_bpure.ROWS rank tl mtl maxW (TT - (tl + 1 - maxW) + 1) 1 rv' ->
       evtF bsegs RNG POST (STQ m2 maxW yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30)) ->
    evtF bsegs RNG POST (STI m1 maxW c w xra x7 xa0 xa1 x28).
  Proof.
    induction f as [|f IH]; intros until x28; intros I HMW HIGH HC HW HF RRW KX; [lia|].
    pose proof STATS as (TLR & _). assert (MTL12 : mtl <= 12) by (open_hx2b HY; lia).
    eapply x2_wi_bodyB; [exact I| exact HMW| exact HIGH| exact HC| exact HW| exact RRW| | |].
    - intros m2 rv' y7 ya0 ya1 y28 HN I2 RRW2. eapply IH; [exact I2| exact HMW| exact HIGH| lia| lia| lia| exact RRW2| exact KX].
    - intros m2 rv' y7 ya0 ya1 y28 EW HN I2 RRW2. eapply IH; [exact I2| exact HMW| exact HIGH| lia| lia| lia| exact RRW2| exact KX].
    - intros m2 rv' yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 EW EC I2 RRW2.
      eapply KX; [exact I2| rewrite <- EC; exact RRW2].
  Qed.

  Definition x2_rsortB_stmt : Prop :=
    forall m1 (dt rs0 rv : list Z) (syb : list byte) xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31,
    XBP k16 k8 k336 k136 k0 k368 k144 k120 dt rs0 syb rv m1 ->
    (forall m2 (maxW : Z) (rs0' rv' : list Z) (syb' : list byte) yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30,
       1 <= maxW <= tl -> (forall v, maxW < v <= 12 -> Znth v rank = 0) ->
       AF_huf_x2t_bpure.RSF rank maxW rs0' -> AF_huf_x2t_bpure.RVX rank tl mtl maxW rv' ->
       XBW maxW dt rs0' syb' rv' m2 ->
       evtF bsegs RNG POST (STQ m2 maxW yra y5 y6 y7 ya0 ya1 ya4 ya5 ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30)) ->
    evtF bsegs RNG POST (ST0 m1 xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31).

  Lemma x2_rsortB : x2_rsortB_stmt.
  Proof.
    unfold x2_rsortB_stmt. intros until x31; intros I K. pose proof STATS as (TLR & _).
    assert (MTL12 : mtl <= 12) by (open_hx2b HY; lia).
    pose proof (TTB_range tl mtl ltac:(lia) ltac:(lia)) as TTR.
    eapply x2_p1aB; try eassumption. intros m2 ya1 ya5 I2.
    eapply x2_m_loopB with (f := Z.to_nat tl); try eassumption; try lia;
      [intros v Hv; eapply x2w_rank_hi; eauto; lia |].
    intros maxW yb5 yb6 yb7 HMW HNZ HIGH.
    eapply x2_p1bB; try eassumption; try lia. intros yb2.
    eapply x2_r_loopB with (f := Z.to_nat (maxW + 1)); try eassumption; try lia;
      [rewrite xs1_1; reflexivity | intros v Hv; lia |].
    intros m3 rs1 yc2 yc5 yc30 I3 RI3.
    assert (RL1 : zlen rs1 = 15) by (open_xbb I3; exact RS0LEN).
    eapply x2_p1cB; try eassumption; try lia. intros m4 yd1 I4.
    eapply x2_s_loopB with (f := Z.to_nat nbs); try eassumption; try lia.
    { eapply sinv0.
      - intros v Hv. rewrite !Znth_Zupd_other by lia. apply RI3. lia.
      - rewrite Znth_Zupd_other by lia. apply Znth_Zupd_same. unfold FseNCount.Zlength. lia. }
    intros m6 rs3 syb3 ye1 ye30 ye31 I5 SI5.
    assert (RL3 : zlen rs3 = 15) by (open_xbb I5; exact RS0LEN).
    assert (RSF3 : AF_huf_x2t_bpure.RSF rank maxW (Zupd 1 0 rs3)) by (eapply rsf_of_sinv; eauto).
    eapply x2_e_headB; try eassumption; try lia. intros m7 yf7 yf1 yf28 I6.
    eapply x2_v_loopB with (f := Z.to_nat (maxW + 1)); try eassumption; try lia; [intros v Hv; lia |].
    intros m8 rv1 yg7 yg1 yg28 I7 VI7.
    eapply x2_w_entryB; try eassumption; try lia.
    - intros m9 yh7 yh0 yh1 yh28 HC I8.
      eapply x2_wi_loopB with (f := Z.to_nat 169); try eassumption; try lia;
        [eapply (rows0 hw); [lia| exact VI7] |].
      intros m10 rv2 yra y5 y6 y7 ya0 ya1' ya4 ya5' ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 I9 RW9.
      eapply K; [lia| exact HIGH| exact RSF3| eapply (rvx_of_rows hw); exact RW9| exact I9].
    - intros m9 yra y5 y6 y7 ya0 ya1' ya4 ya5' ya6 ya7 ys2 ys6 ys8 ys9 ys10 ys11 y28 y29 y30 HN I8.
      eapply K; [lia| exact HIGH| exact RSF3| eapply (rvx_of_rows hw); eapply (rows0 hw); [lia| exact VI7]| exact I8].
  Qed.


End X2B.
End CANSEC1.
