(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells FsKit AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg
  AF_huf_x2t_bgeo AF_huf_x2t_bdefs AF_huf_x2t_hdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXSound KXGoF FseWalkMem.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_enrich ::= rewrite ?shad_div in *; rewrite ?nshad_div in *; unfold ASHOFF, KLOW, KHIGH, KEND in *; rewrite ?Z.shiftr_div_pow2 in * by lia.

Ltac pcoff := lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?n) _ _ _ _) => let p := eval vm_compute in (n - 0x81e48) in p end.
Ltac at_stop stops := let p := pcoff in let b := eval vm_compute in (existsb (Z.eqb p) stops) in
  lazymatch b with true => idtac | false => fail end.
Ltac walk stops := repeat (tryif at_stop stops then fail else (zstep)).
Ltac is_ifpc := lazymatch goal with |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => idtac end.

Definition HideP (P : Prop) : Prop := P.
Ltac hide_disj := repeat match goal with H : ?A \/ ?B |- _ => change (HideP (A \/ B)) in H end.
Ltac hide_cells := repeat match goal with H : rw_cells _ _ _ _ |- _ => let t := type of H in change (HideP t) in H end.

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

  Lemma b3w_land : Z.land hdw (2^64 - 2^24) = B3W.
  Proof.
    rewrite (KXS.land_highmask hdw 24) by lia. rewrite (Z.mod_small hdw (2^64)) by lia.
    pose proof (Z.div_mod hdw 16777216 ltac:(lia)). change (2^24) with 16777216. lia.
  Qed.

  Lemma TT_cases : (tl <= 11 /\ 11 < mtl /\ TT = 11) \/ (~ (tl <= 11 /\ 11 < mtl) /\ TT = mtl).
  Proof. unfold TTB. destruct (Z.leb_spec tl 11), (Z.ltb_spec 11 mtl); cbn; lia. Qed.

  Notation XBP1 dt rs0 syb rv mm :=
    (XBP (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 B3W) k368 k144 k120 dt rs0 syb rv mm) (only parsing).

  Lemma x2w_sh0 : forall m lo hi a, unpoisoned m lo hi -> lo <= a -> 8 * (a / 8) + 8 <= hi -> 0 <= a < 2^64 ->
    ov_read_bytes bsegs m (wa (Z.shiftr (a mod 2^64) 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros m lo0 hi a U L H R. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
    replace (a / 8 + ASHOFF) with (ASHOFF + a / 8) by lia.
    eapply unpoisoned_full_rd; [exact U| rewrite shad_div; pose proof (Z.div_le_mono lo0 a 8 ltac:(lia) L); lia| lia].
  Qed.

  Lemma x2w_unp_wk : forall m1, munch [(DT, DT + 4 * (1 + 2 ^ mtl)); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1 ->
    unpoisoned m1 WK (WK + wksz).
  Proof.
    intros m1 MU. open_hx2b HY.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABD, ABW. unfold KHIGH in KLO.
    pose proof (x2b_dtbB mtl MTL) as DTBR.
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. repeat split; Z.div_mod_to_equations; lia.
  Qed.

  Lemma x2w_acc_sh : forall a, WK <= a < WK + wksz -> acc_in RNG (Z_to_bv 64 (Z.shiftr (a mod 18446744073709551616) 3 + ASHOFF), 1%nat).
  Proof. intros a Ha. open_hx2b HY. rewrite Z.mod_small by lia. solve_acc_with RSW. Qed.

  Lemma x2w_acc_wk4 : forall a, WK <= a -> a + 4 <= WK + wksz -> acc_in RNG (Z_to_bv 64 a, 4%nat).
  Proof. intros a H1 H2. open_hx2b HY. solve_acc_with RW. Qed.

  Lemma x2w_rk_rd : forall m v, u32arr bsegs m (WK + 624) (map (Z_to_bv 64) rank) -> 0 <= v <= 12 ->
    ov_read_bytes bsegs m (wa (WK + 624 + Z.shiftl v 2)) 4 = Some (le4 (Z_to_bv 64 (Znth v rank))).
  Proof.
    intros m v RK0 Hv. eapply u32arr_read; [exact RK0| apply nth_error_map_Znth; lia| lia| rewrite Z.shiftl_mul_pow2 by lia; f_equal; lia].
  Qed.

  Ltac x2w_prune K :=
    try ((exfalso; lia));
    try ((exfalso; rewrite ?Z.shiftl_mul_pow2 in K by lia; lia));
    try ((exfalso; rewrite ?KXS.swrap32_small in K by lia; rewrite ?Z.mod_small in K by lia; lia));
    try ((exfalso; lazymatch type of K with context [bv_unsigned (sxb (Z_to_bv 8 ?c))] =>
                      rewrite (sxb_lit c) in K by lia; cbn in K; lia end)).
  Ltac x2w_go stops :=
    walk stops;
    try (is_ifpc; let K := fresh "K" in bcase K; x2w_prune K; x2w_go stops).

  Lemma x2w_rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & LW & _ & _ & RC & _). rewrite RC by lia. unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)). unfold FseNCount.Zlength in LW. lia.
  Qed.

  Lemma x2w_rank_some : forall w, 1 <= w <= 12 -> Znth w rank = 0 -> (forall v, w < v <= 12 -> Znth v rank = 0) -> 1 <= w - 1.
  Proof.
    intros w Hw H0 HZ. destruct (Z.eq_dec w 1) as [->|NE]; [| lia]. exfalso.
    pose proof STATS as (TLR & _).
    apply (some_weight _ rank tl 12 STATS ltac:(lia)). intros v Hv. destruct (Z.eq_dec v 1) as [->|NE]; [exact H0| apply HZ; lia].
  Qed.

  Notation STME mm maxW xra x5 x6 x7 xa5 xa6 xa7 x28 x29 x30 x31 :=
    (ST 0x82140 mm xra x5 x6 x7 (Z_to_bv 64 (WK + 680)) (Z_to_bv 64 (Znth maxW rank)) (Z_to_bv 64 (2^64 - 1 - (WK + 624))) (Z_to_bv 64 13)
        (Z_to_bv 64 (tl - maxW)) xa5 xa6 xa7
        (Z_to_bv 64 TT) (Z_to_bv 64 hdw) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32)) x28 x29 x30 x31)
    (only parsing).

  Lemma x2_p1aB : forall m1 (dt rs0 rv : list Z) (syb : list byte) xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31,
    XBP k16 k8 k336 k136 k0 k368 k144 k120 dt rs0 syb rv m1 ->
    (forall m2 (ya1 ya5 : word),
       XBP (Z_to_bv 64 r) (Z_to_bv 64 mtl) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 B3W) k368 k144 k120 dt rs0 syb rv m2 ->
       evtF bsegs RNG POST (STM m2 tl 0 xra x5 x6 x7 ya1 ya5 xa6 xa7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (ST0 m1 xra x5 x6 x7 xa0 xa4 xa5 xa6 xa7 xsrc x28 x29 x30 x31).
  Proof.
    intros until x31; intros I K. open_xbb I. open_hx2b HY. hide_disj.
    pose proof STATS as (TLR & _). pose proof TT_cases as TTC. pose proof b3w_land as B3.
    pose proof (munch_refl [(SPA, SPA + 408)] m1) as MU1. pose proof (wmono_refl bsegs m1) as WM1.
    change (HideP (u8arr bsegs m1 DT (map (Z_to_bv 8) dt))) in DTC. change (HideP (u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw))) in HWC.
    change (HideP (u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank))) in RK. change (HideP (u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0))) in RS0.
    change (HideP (u8arr bsegs m1 (WK + 736) syb)) in SYC. change (HideP (u32arr bsegs m1 WK (map (Z_to_bv 64) rv))) in RV.
    x2w_go [684; 3916].
    all: unfold HideP in *.
    all: lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => transport_after_call bsegs m1 mm MU1 WM1 end.
    all: try kx_mkR_foldF.
    all: lazymatch goal with |- context [Z.lxor (WK + 624) ?c] => change c with (2^64 - 1) end.
    all: rewrite (KXS.lxor_ones64 (WK + 624)) by lia.
    all: lazymatch type of FR with context [Z.land hdw ?c] => change c with (2^64 - 2^24) in FR end.
    all: rewrite B3 in FR.
    all: lazymatch goal with |- evtF _ _ _ (MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?s2 _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) =>
           replace s2 with (Z_to_bv 64 TT) by (f_equal; lia) end.
    all: eapply K; close_xbb.
  Qed.
  Lemma x2_m_bodyB : forall m1 (dt rs0 rv : list Z) (syb : list byte) (w cnt : Z) xra x5 x6 x7 xa1 xa5 xa6 xa7 x28 x29 x30 x31,
    XBP1 dt rs0 syb rv m1 ->
    1 <= w <= tl -> cnt = tl - w -> (forall v, w < v <= 12 -> Znth v rank = 0) ->
    (forall (ya1 ya5 ya6 ya7 : word), 1 <= w - 1 -> Znth w rank = 0 -> (forall v, w - 1 < v <= 12 -> Znth v rank = 0) ->
       evtF bsegs RNG POST (STM m1 (w - 1) (cnt + 1) xra x5 x6 x7 ya1 ya5 ya6 ya7 x28 x29 x30 x31)) ->
    (forall (ya5 ya6 ya7 : word), Znth w rank <> 0 ->
       evtF bsegs RNG POST (STME m1 w xra x5 x6 x7 ya5 ya6 ya7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STM m1 w cnt xra x5 x6 x7 xa1 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HW HC HZ KH KE. open_xbb I. open_hx2b HY. hide_disj. subst cnt.
    pose proof STATS as (TLR & _). pose proof (x2w_rank_small w ltac:(lia)) as RW0.
    pose proof (x2w_unp_wk m1 MU) as UW1.
    assert (HSH : ov_read_bytes bsegs m1 (wa (Z.shiftr ((WK + 624 + Z.shiftl w 2) mod 18446744073709551616) 3 + ASHOFF)) 1 = Some [Z_to_bv 8 0])
      by (apply (x2w_sh0 m1 WK (WK + wksz)); [exact UW1| rewrite Z.shiftl_mul_pow2 by lia; lia..]).
    pose proof (x2w_acc_sh (WK + 624 + Z.shiftl w 2) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)) as HAC1.
    pose proof (x2w_acc_wk4 (WK + 624 + Z.shiftl w 2) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia) ltac:(rewrite Z.shiftl_mul_pow2 by lia; lia)) as HAC2.
    pose proof (x2w_rk_rd m1 w RK ltac:(lia)) as HRK.
    hide_cells.
    zstep; x2w_go [684; 760; 3916]; unfold HideP in *; try kx_mkR_foldF;
    repeat match goal with H : context [sx32 (Z_to_bv 64 (Znth w rank))] |- _ => rewrite (sx32_small (Znth w rank)) in H by lia end;
    rewrite ?(sx32_small (Znth w rank)) by lia;
    rewrite ?unsigned_lit in * by lia;
    rewrite ?KXS.swrap32_small by lia;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x82140) _ _ _ _) => eapply KE; lia
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x820f4) _ _ _ _) =>
        replace (w + -1) with (w - 1) by lia;
        assert (R0 : Znth w rank = 0) by lia;
        eapply KH; [apply x2w_rank_some; [lia|exact R0|exact HZ] | exact R0 | intros v Hv; destruct (Z.eq_dec v w) as [->|NE]; [exact R0| apply HZ; lia]]
    end.
  Qed.

  Lemma x2_m_loopB : forall (f : nat) m1 (dt rs0 rv : list Z) (syb : list byte) (w cnt : Z) xra x5 x6 x7 xa1 xa5 xa6 xa7 x28 x29 x30 x31,
    XBP1 dt rs0 syb rv m1 ->
    1 <= w <= tl -> w <= Z.of_nat f -> cnt = tl - w -> (forall v, w < v <= 12 -> Znth v rank = 0) ->
    (forall (maxW : Z) (ya5 ya6 ya7 : word), 1 <= maxW <= w -> Znth maxW rank <> 0 -> (forall v, maxW < v <= 12 -> Znth v rank = 0) ->
       evtF bsegs RNG POST (STME m1 maxW xra x5 x6 x7 ya5 ya6 ya7 x28 x29 x30 x31)) ->
    evtF bsegs RNG POST (STM m1 w cnt xra x5 x6 x7 xa1 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    induction f; intros until x31; intros I HW HF HC HZ KE; [lia|].
    eapply x2_m_bodyB; [exact I | exact HW | exact HC | exact HZ | |].
    - intros ya1 ya5 ya6 ya7 H1 H0 HZ'. eapply IHf; [exact I | lia | lia | lia | exact HZ' |].
      intros maxW y5 y6 y7 HMW HN HZ''. eapply KE; [lia | exact HN | exact HZ''].
    - intros ya5 ya6 ya7 HN. eapply KE; [lia | exact HN | exact HZ].
  Qed.

  Lemma x2w_rank_hi : forall v, tl < v <= 12 -> Znth v rank = 0.
  Proof.
    intros v Hv. destruct STATS as (TLR & _ & FW & _ & RC & _). rewrite RC by lia. unfold hcount.
    rewrite (proj1 (count_occ_not_In Z.eq_dec _ v)); [reflexivity|]. intros IN. rewrite Forall_forall in FW. specialize (FW v IN). lia.
  Qed.

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
  Ltac x2w_shload := lazymatch goal with |- context [ov_read_bytes bsegs ?m (Z_to_bv 64 (Z.shiftr ?a 3 + ASHOFF)) 1%nat] =>
      lazymatch goal with U : unpoisoned m ?lo0 ?hi |- _ => rewrite (x2w_sh0n m lo0 hi a U) by x2w_side end end; load_post.
  Ltac x2w_acchint := lazymatch goal with
    | |- acc_in _ (Z_to_bv 64 (Z.shiftr ?a 3 + ASHOFF), 1%nat) =>
        lazymatch goal with H : rng _ (shad WK) _ |- _ => eapply (x2w_acc_rng _ _ _ _ H); x2w_side end
    | |- acc_in _ (Z_to_bv 64 ?a, ?n) =>
        lazymatch goal with H : rng _ WK wksz |- _ => eapply (x2w_acc_rng _ _ _ _ H); x2w_side end
    end.
  Local Ltac solve_load ::= first [ x2w_shload | solve_load_base | solve_load_image ].
  Local Ltac acc_hint ::= x2w_acchint.

  Lemma x2w_Forall_Zupd : forall (P : Z -> Prop) l i v, Forall P l -> P v -> Forall P (Zupd i v l).
  Proof.
    intros P l i v H Hv. unfold Zupd. generalize (Z.to_nat i) as n. revert H.
    induction l as [|x l IH]; intros H n; destruct n; cbn; inversion H; subst; constructor; auto.
  Qed.

  Lemma x2w_xbb_rs0 : forall v16 v8 v336 v136 v0 v368 v144 v120 m1 (dt rs0 rv : list Z) (syb : list byte) i v,
    XBP v16 v8 v336 v136 v0 v368 v144 v120 dt rs0 syb rv m1 -> 0 <= i < 15 -> 0 <= v < 2^32 ->
    XBP v16 v8 v336 v136 v0 v368 v144 v120 dt (Zupd i v rs0) syb rv (write_to_mem m1 (wa (WK + 676 + 4 * i)) (le4 (Z_to_bv 64 v))).
  Proof.
    intros until v; intros I HI HV. open_xbb I. open_hx2b HY.
    pose proof (x2b_dtbB mtl MTL) as DTBR.
    assert (RS0' : u32arr bsegs (write_to_mem m1 (wa (WK + 676 + 4 * i)) (le4 (Z_to_bv 64 v))) (WK + 676) (map (Z_to_bv 64) (Zupd i v rs0))).
    { unfold Zupd. rewrite map_upd_nat. apply u32arr_write; [exact RS0| rewrite length_map; lia]. }
    assert (HS : store_ok bsegs m1 (wa (WK + 676 + 4 * i)) 4 = true)
      by (eapply (u32arr_store_ok bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0) i); [exact RS0| rewrite length_map; lia| reflexivity]).
    apply (mem_inv_store bsegs m1 (wa (WK + 676 + 4 * i)) (le4 (Z_to_bv 64 v))) in MI; [| exact HS].
    clear RS0.
    transport_chunks bsegs m1 (WK + 676 + 4 * i) (le4 (Z_to_bv 64 v)).
    footprint_after_store bsegs m1 (WK + 676 + 4 * i) (le4 (Z_to_bv 64 v)).
    close_xbb.
    - rewrite Zupd_length. exact RS0LEN.
    - apply x2w_Forall_Zupd; [exact RS0NN| lia].
  Qed.

  Notation XS1 w := (xs1 rank w).
  Definition x2w_rinv (w : Z) (rs0 : list Z) : Prop := forall v, 1 <= v < w -> Znth (v + 1) rs0 = XS1 v.

  Lemma x2w_xs1_bounds : forall w, 1 <= w <= 13 -> 0 <= XS1 w <= 256.
  Proof.
    intros w Hw. pose proof STATS as (TLR & LW & _).
    pose proof (xs1_mono (firstn (Z.to_nat nbs) hw) rank tl STATS 1 w ltac:(lia) ltac:(lia)) as M1.
    pose proof (xs1_mono (firstn (Z.to_nat nbs) hw) rank tl STATS w 13 ltac:(lia) ltac:(lia)) as M2.
    pose proof (xs1_top (firstn (Z.to_nat nbs) hw) rank tl STATS) as T.
    pose proof (xs1_1 rank) as X1. pose proof (x2w_rank_small 0 ltac:(lia)) as R0. lia.
  Qed.

  Ltac x2w_regeq := lazymatch goal with
    | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia
        | f_equal; try (lazymatch goal with |- context [Z.lxor ?x ?c] => change c with (2^64 - 1); rewrite (KXS.lxor_ones64 x) by lia end);
          rewrite ?KXS.swrap32_small by lia; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia;
          repeat rewrite (Z.mod_small _ (2^32)) by lia; repeat rewrite Z.mod_small by lia; Z.div_mod_to_equations; lia ]
    | |- _ => reflexivity end.
  Ltac x2w_eqs := f_equal; try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ => f_equal; x2w_regeq end).

  Notation STRp pc mm maxW w acc xra xa2 xa5 x29 x30 x31 :=
    (ST pc mm xra (Z_to_bv 64 (WK + 680 + 4 * w)) (Z_to_bv 64 (4 * (maxW + 1))) (Z_to_bv 64 (4 * w))
       (Z_to_bv 64 (WK + 680)) (Z_to_bv 64 (WK + 680 + 4 * w)) xa2 (Z_to_bv 64 (Z.shiftl (maxW + 1) 32)) (Z_to_bv 64 (tl - maxW)) xa5
       (Z_to_bv 64 (2^64 - 1 - (WK + 680))) (Z_to_bv 64 (maxW + 1))
       (Z_to_bv 64 TT) (Z_to_bv 64 hdw) (Z_to_bv 64 maxW) (Z_to_bv 64 (FF + 48)) (Z_to_bv 64 WK) (Z_to_bv 64 (WK + 992)) xs9 (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 (FF + 32))
       (Z_to_bv 64 acc) x29 x30 x31) (only parsing).
  Notation STR mm maxW w acc xra xa2 xa5 x29 x30 x31 := (STRp 0x8216c mm maxW w acc xra xa2 xa5 x29 x30 x31) (only parsing).
  Notation STR2 mm maxW tot xra xa2 xa5 x29 x30 x31 := (STRp 0x821e0 mm maxW (maxW + 1) tot xra xa2 xa5 x29 x30 x31) (only parsing).

  Lemma x2_p1bB : forall m1 (dt rs0 rv : list Z) (syb : list byte) (maxW : Z) xra x5 x6 x7 xa5 xa6 xa7 x28 x29 x30 x31,
    XBP1 dt rs0 syb rv m1 -> 1 <= maxW <= tl ->
    (forall (ya2 : word), evtF bsegs RNG POST (STR m1 maxW 1 0 xra ya2 xa5 x29 x30 x31)) ->
    evtF bsegs RNG POST (STME m1 maxW xra x5 x6 x7 xa5 xa6 xa7 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I HW K. open_xbb I. open_hx2b HY. hide_disj.
    pose proof STATS as (TLR & _).
    zstep; x2w_go [804; 916; 3916]; unfold HideP in *; try kx_mkR_foldF;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x8216c) _ _ _ _) =>
        match goal with |- evtF _ _ _ ?s => eassert (EQS : _ = s); [| rewrite <- EQS; eapply K] end;
        x2w_eqs
    end.
  Qed.

End X2B.
End CANSEC1.
