(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg
  AF_huf_x2t_bgeo AF_huf_x2t_bdefs AF_huf_x2t_hdefs AF_huf_x2t_bp1.
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

  Lemma x2_r_bodyB : forall m1 (dt rs0 rv : list Z) (syb : list byte) (maxW w acc : Z) xra xa2 xa5 x29 x30 x31,
    XBP1 dt rs0 syb rv m1 ->
    1 <= maxW <= tl -> 1 <= w <= maxW -> acc = XS1 w -> RINV w rs0 ->
    (forall m2 (rs0' : list Z) (ya2 ya5 y29 y30 : word), w + 1 <= maxW -> XBP1 dt rs0' syb rv m2 -> RINV (w + 1) rs0' ->
       evtF bsegs RNG POST (STR m2 maxW (w + 1) (XS1 (w + 1)) xra ya2 ya5 y29 y30 x31)) ->
    (forall m2 (rs0' : list Z) (ya2 ya5 y30 : word), w = maxW -> XBP1 dt rs0' syb rv m2 -> RINV (maxW + 1) rs0' ->
       evtF bsegs RNG POST (STR2 m2 maxW (XS1 (maxW + 1)) xra ya2 ya5 y30 x31)) ->
    evtF bsegs RNG POST (STR m1 maxW w acc xra xa2 xa5 x29 x30 x31).
  Proof.
    intros until x31; intros I HMW HW HA RIV KH KE. subst acc. pose proof STATS as (TLR & _).
    assert (XB0 : 0 <= XS1 w <= 256) by (eapply x2w_xs1_bounds; eauto; lia).
    assert (I2 : XBP1 dt (Zupd (w + 1) (XS1 w) rs0) syb rv (write_to_mem m1 (wa (WK + 676 + 4 * (w + 1))) (le4 (Z_to_bv 64 (XS1 w)))))
      by (eapply x2w_xbb_rs0; eauto; lia).
    assert (RIV2 : RINV (w + 1) (Zupd (w + 1) (XS1 w) rs0)).
    { intros v Hv. open_xbb I. destruct (Z.eq_dec v w) as [->|NE].
      - apply Znth_Zupd_same. unfold FseNCount.Zlength. lia.
      - rewrite Znth_Zupd_other by lia. apply RIV. lia. }
    open_xbb I. open_hx2b HY. hide_disj.
    assert (RW0 : 0 <= Znth w rank <= 256) by (eapply x2w_rank_small; eauto; lia).
    pose proof (xs1_step rank w ltac:(lia)) as XST.
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x2w_unp_wk; eauto).
    pose proof (x2v_u32rd m1 (WK + 624) rank (WK + 680 + 4 * w + -56) w RK ltac:(lia) ltac:(lia)) as HRK.
    assert (HS : store_ok bsegs m1 (wa (WK + 680 + 4 * w)) 4 = true)
      by (eapply (u32arr_store_ok bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0) (w + 1)); [exact RS0| rewrite length_map; lia| f_equal; lia]).
    hide_cells.
    zstep; x2v_go [804; 920; 3916]; unfold HideP in *; try kx_mkR_foldF;
    rewrite ?(sx32_small (Znth w rank)) by lia; rewrite ?unsigned_lit by lia; 
    replace (write_to_mem m1 (Z_to_bv 64 (WK + 680 + 4 * w)) (le4 (Z_to_bv 64 (XS1 w))))
      with (write_to_mem m1 (wa (WK + 676 + 4 * (w + 1))) (le4 (Z_to_bv 64 (XS1 w)))) by (unfold wa; f_equal; f_equal; lia);
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8216c) _ _ _ _) =>
        match goal with |- evtF _ _ _ ?s => eassert (EQS : _ = s); [| rewrite <- EQS; eapply KH; [lia| exact I2| exact RIV2]] end;
        x2v_eqs
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x821e0) _ _ _ _) =>
        assert (EW : maxW = w) by lia; subst maxW;
        match goal with |- evtF _ _ _ ?s => eassert (EQS : _ = s); [| rewrite <- EQS; eapply KE; [lia| exact I2| exact RIV2]] end;
        x2v_eqs
    end.
  Qed.

  Lemma x2_r_loopB : forall (f : nat) m1 (dt rs0 rv : list Z) (syb : list byte) (maxW w acc : Z) xra xa2 xa5 x29 x30 x31,
    XBP1 dt rs0 syb rv m1 ->
    1 <= maxW <= tl -> 1 <= w <= maxW -> maxW + 1 - w <= Z.of_nat f -> acc = XS1 w -> RINV w rs0 ->
    (forall m2 (rs0' : list Z) (ya2 ya5 y30 : word), XBP1 dt rs0' syb rv m2 -> RINV (maxW + 1) rs0' ->
       evtF bsegs RNG POST (STR2 m2 maxW (XS1 (maxW + 1)) xra ya2 ya5 y30 x31)) ->
    evtF bsegs RNG POST (STR m1 maxW w acc xra xa2 xa5 x29 x30 x31).
  Proof.
    induction f as [|f IH]; intros until x31; intros I HMW HW HF HA RIV KE; [lia|].
    eapply x2_r_bodyB; [exact I| exact HMW| exact HW| exact HA| exact RIV| |].
    - intros m2 rs0' ya2 ya5 y29 y30 HW1 I2 RI2. eapply IH; [exact I2| exact HMW| lia| lia| reflexivity| exact RI2| exact KE].
    - intros m2 rs0' ya2 ya5 y30 EW I2 RI2. eapply KE; [exact I2| exact RI2].
  Qed.

  Notation STS mm maxW s xra xa1 xa2 xa5 x30 x31 :=
    (ST 0x82238 mm xra (Z_to_bv 64 s) (Z_to_bv 64 (2^64 - 1 - (WK + 992))) (Z_to_bv 64 (2^64 - 1 - (WK + 736)))
       (Z_to_bv 64 (WK + 680)) xa1 xa2 (Z_to_bv 64 (Z.shiftl (maxW + 1) 32)) (Z_to_bv 64 (tl - maxW)) xa5
       (Z_to_bv 64 (2^64 - 1 - (WK + 680))) (Z_to_bv 64 nbs)
       (Z_to_bv 64 TT) (Z_to_bv 64 hdw) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32))
       (Z_to_bv 64 256) (Z_to_bv 64 255) x30 x31) (only parsing).

  Lemma x2_p1cB : forall m1 (dt rs0 rv : list Z) (syb : list byte) (maxW : Z) xra xa2 xa5 x30 x31,
    XBP1 dt rs0 syb rv m1 -> 1 <= maxW <= tl -> RINV (maxW + 1) rs0 ->
    (forall m2 (ya1 : word), XBP1 dt (Zupd (maxW + 2) (XS1 (maxW + 1)) (Zupd 1 (XS1 (maxW + 1)) rs0)) syb rv m2 ->
       evtF bsegs RNG POST (STS m2 maxW 0 xra ya1 (Z_to_bv 64 (Z.shiftr (WK + 680) 3 + ASHOFF)) xa5 x30 x31)) ->
    evtF bsegs RNG POST (STR2 m1 maxW (XS1 (maxW + 1)) xra xa2 xa5 x30 x31).
  Proof.
    intros until x31; intros I HMW RIV K. pose proof STATS as (TLR & _).
    assert (XB0 : 0 <= XS1 (maxW + 1) <= 256) by (eapply x2w_xs1_bounds; eauto; lia).
    assert (I2 : XBP1 dt (Zupd 1 (XS1 (maxW + 1)) rs0) syb rv (write_to_mem m1 (Z_to_bv 64 (WK + 680)) (le4 (Z_to_bv 64 (XS1 (maxW + 1))))))
      by (replace (Z_to_bv 64 (WK + 680)) with (wa (WK + 676 + 4 * 1)) by (unfold wa; f_equal; lia); eapply x2w_xbb_rs0; eauto; lia).
    open_xbb I. open_hx2b HY. hide_disj.
    assert (UW1 : unpoisoned m1 WK (WK + wksz)) by (eapply x2w_unp_wk; eauto).
    assert (HS : store_ok bsegs m1 (wa (WK + 680)) 4 = true)
      by (eapply (u32arr_store_ok bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0) 1); [exact RS0| rewrite length_map; lia| f_equal; lia]).
    zstep; x2v_go [968; 1008; 1168; 3916].
    unfold HideP in *.
    set (m2 := write_to_mem m1 (Z_to_bv 64 (WK + 680)) (le4 (Z_to_bv 64 (XS1 (maxW + 1))))) in *. clearbody m2.
    clear DTC DTLEN DTBY HWC RK RS0 RS0LEN RS0NN SYC SYLEN RV RVLEN RVNN WKR NBC STK MI MU WM FR HS UW1.
    open_xbb I2. hide_disj.
    assert (UW2 : unpoisoned m2 WK (WK + wksz)) by (eapply x2w_unp_wk; eauto).
    assert (HS2 : store_ok bsegs m2 (wa (WK + 680 + Z.shiftl (maxW + 1) 2)) 4 = true)
      by (eapply (u32arr_store_ok bsegs m2 (WK + 676) (map (Z_to_bv 64) (Zupd 1 (XS1 (maxW + 1)) rs0)) (maxW + 2));
          [exact RS0| rewrite length_map; lia| f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia]).
    zstep.
    assert (I3 : XBP1 dt (Zupd (maxW + 2) (XS1 (maxW + 1)) (Zupd 1 (XS1 (maxW + 1)) rs0)) syb rv
                   (write_to_mem m2 (Z_to_bv 64 (WK + 680 + Z.shiftl (maxW + 1) 2)) (le4 (Z_to_bv 64 (XS1 (maxW + 1))))))
      by (replace (Z_to_bv 64 (WK + 680 + Z.shiftl (maxW + 1) 2)) with (wa (WK + 676 + 4 * (maxW + 2)))
            by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia);
          eapply x2w_xbb_rs0; eauto; lia).
    set (m3 := write_to_mem m2 (Z_to_bv 64 (WK + 680 + Z.shiftl (maxW + 1) 2)) (le4 (Z_to_bv 64 (XS1 (maxW + 1))))) in *. clearbody m3.
    clear DTC DTLEN DTBY HWC RK RS0 RS0LEN RS0NN SYC SYLEN RV RVLEN RVNN WKR NBC STK MI MU WM FR HS2 UW2.
    open_xbb I3. hide_disj.
    assert (UW3 : unpoisoned m3 WK (WK + wksz)) by (eapply x2w_unp_wk; eauto).
    zstep; x2v_go [1008; 1168; 3916]; unfold HideP in *; try kx_mkR_foldF;
    unfold zx32; rewrite (unsigned_lit nbs) by lia; rewrite (Z.mod_small nbs) by lia;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x82238) _ _ _ _) =>
        match goal with |- evtF _ _ _ ?s => eassert (EQS : _ = s); [| rewrite <- EQS; eapply K; exact I3] end;
        x2v_eqs
    end.
  Qed.

End X2B.
End CANSEC1.
