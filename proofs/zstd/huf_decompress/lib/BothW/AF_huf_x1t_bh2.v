(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import DrvAgree FseRdKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells AProto AMalloc_iface AFake0k_iface AProg_kit
     AFake_arep FsKit AF_fse_rd_iface AF_fse_rd_base AF_fse_rd_mem AF_fse_rd_seg AF_fse_rd_asm AH_huf_kit AH_huf_iface
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AF_huf_x1t_bdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import ZdHufStats ZdHufX1.

Lemma u32b_firstn : forall k l, firstn (4 * k) (u32b l) = u32b (firstn k l).
Proof.
  induction k as [|k IH]; intros [|x l]; try reflexivity.
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [firstn u32b u32q app]. rewrite IH. reflexivity.
Qed.
Lemma u32b_skipn : forall k l, skipn (4 * k) (u32b l) = u32b (skipn k l).
Proof.
  induction k as [|k IH]; intros [|x l]; try reflexivity.
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [skipn u32b u32q app]. rewrite IH. reflexivity.
Qed.
Lemma u32b_repeat0 : forall k, u32b (repeat 0 k) = repeat 0 (4 * k).
Proof.
  induction k as [|k IH]; [reflexivity|].
  replace (4 * S k)%nat with (S (S (S (S (4 * k)))))%nat by lia. cbn [repeat u32b u32q app]. rewrite IH. reflexivity.
Qed.
Lemma map_repeat' : forall {A B} (f : A -> B) (a : A) k, map f (repeat a k) = repeat (f a) k.
Proof. intros A B f a k. induction k as [|k IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma land_m1_l : forall s, 0 <= s < 18446744073709551616 -> Z.land 18446744073709551615 s = s.
Proof. intros s Hs. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma u32b_resc_split : forall (rk0 : list Z) (sc0 : Z), Z.of_nat (length rk0) = 13 -> 0 <= sc0 <= 12 ->
  map (Z_to_bv 8) (u32b ([Znth 0 rk0] ++ repeat 0 (Z.to_nat sc0) ++ skipn (Z.to_nat (sc0 + 1)) rk0))
  = firstn 4 (map (Z_to_bv 8) (u32b rk0)) ++ (repeat (Z_to_bv 8 0) (Z.to_nat (4 * sc0)) ++ skipn (Z.to_nat (4 * sc0)) (skipn 4 (map (Z_to_bv 8) (u32b rk0)))).
Proof.
  intros rk0 sc0 L Hs. rewrite !u32b_app, !map_app. destruct rk0 as [|x t]; [cbn in L; lia|].
  assert (E1 : map (Z_to_bv 8) (u32b [Znth 0 (x :: t)]) = firstn 4 (map (Z_to_bv 8) (u32b (x :: t)))).
  { rewrite firstn_map. change 4%nat with (4 * 1)%nat. rewrite u32b_firstn. reflexivity. }
  assert (E2 : map (Z_to_bv 8) (u32b (repeat 0 (Z.to_nat sc0))) = repeat (Z_to_bv 8 0) (Z.to_nat (4 * sc0))).
  { rewrite u32b_repeat0, map_repeat'. f_equal. lia. }
  assert (E3 : map (Z_to_bv 8) (u32b (skipn (Z.to_nat (sc0 + 1)) (x :: t))) = skipn (Z.to_nat (4 * sc0)) (skipn 4 (map (Z_to_bv 8) (u32b (x :: t))))).
  { rewrite skipn_skipn, !skipn_map. replace (Z.to_nat (4 * sc0) + 4)%nat with (4 * Z.to_nat (sc0 + 1))%nat by lia. rewrite u32b_skipn. reflexivity. }
  rewrite E1, E2, E3. reflexivity.
Qed.

Definition zeroed (k sc : Z) (cur0 cur : list Z) : Prop :=
  zlen cur = 13 /\ forall v, 0 <= v <= 12 -> Znth v cur = if (k <? v) && (v <=? sc) then 0 else Znth v cur0.
Lemma zeroed_init : forall sc cur0, zlen cur0 = 13 -> zeroed sc sc cur0 cur0.
Proof. intros sc cur0 L. split; [exact L|]. intros v Hv. destruct (Z.ltb_spec sc v), (Z.leb_spec v sc); cbn [andb]; try reflexivity; lia. Qed.
Lemma zeroed_step : forall k sc cur0 cur, zeroed k sc cur0 cur -> 1 <= k <= sc -> sc <= 12 -> zeroed (k - 1) sc cur0 (Zupd k 0 cur).
Proof.
  intros k sc cur0 cur (L & H) Hk Hs. split; [rewrite Zupd_length; exact L|].
  intros v Hv. destruct (Z.eq_dec v k) as [->|NE].
  - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). destruct (Z.ltb_spec (k - 1) k), (Z.leb_spec k sc); cbn [andb]; first [reflexivity | lia].
  - rewrite Znth_Zupd_other by lia. rewrite H by lia.
    destruct (Z.ltb_spec k v), (Z.ltb_spec (k - 1) v), (Z.leb_spec v sc); cbn [andb]; try reflexivity; lia.
Qed.
Lemma shifted_init_tg : forall tg sc tl rank, FseNCount.Zlength rank = 13 -> tl + sc = tg -> 0 <= sc -> tg <= 11 ->
  (forall v, tl < v <= 12 -> Znth v rank = 0) -> shifted tg sc rank rank.
Proof.
  intros tg sc tl rank L E S T HI. split; [exact L|]. intros v Hv.
  destruct (Z.ltb_spec tg v), (Z.leb_spec v 11); cbn [andb]; try reflexivity. rewrite !HI by lia. reflexivity.
Qed.
Lemma zeroed_resc : forall sc rank cur0 cur tl, shifted sc sc rank cur0 -> zeroed 0 sc cur0 cur -> 0 < sc -> tl + sc <= 11 -> 1 <= tl ->
  (forall v, tl < v <= 12 -> Znth v rank = 0) -> rank_resc sc rank cur.
Proof.
  intros sc rank cur0 cur tl (L0 & H0) (L & H) Hsc HT TL HI. split; [unfold FseNCount.Zlength; exact L|].
  intros v Hv. rewrite H by lia.
  destruct (Z.eqb_spec v 0) as [->|NZ].
  - destruct (Z.ltb_spec 0 0); [lia|]. cbn [andb]. rewrite H0 by lia. destruct (Z.ltb_spec sc 0); [lia | reflexivity].
  - destruct (Z.leb_spec v sc).
    + destruct (Z.ltb_spec 0 v); [|lia]. cbn [andb]. destruct (Z.leb_spec v sc); [reflexivity | lia].
    + destruct (Z.ltb_spec 0 v); cbn [andb]; [| lia]. destruct (Z.leb_spec v sc); [lia|]. rewrite H0 by lia.
      destruct (Z.ltb_spec sc v), (Z.leb_spec v 11); cbn [andb]; try reflexivity; try lia.
      assert (v = 12) by lia. subst v. rewrite (HI 12) by lia. rewrite (HI (12 - sc)) by lia. reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section X1B.
  Variables (RNG : footprint) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m5 : amem) (SPV SPA lo DT DTB WK wksz FF r : Z).
  Hypothesis HY : x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + DTB).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : artcells m5.
  Hypothesis Hr : 0 <= r < 2^32.
  Variable POST : machine_state -> Prop.

  Notation ST pc mm xra x5 x6 x7 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31 :=
    (MS (mkR xra (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPA) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 (Z_to_bv 64 2147450880) xs4
             xs5 xs6 xs7 xs8 xs9 xs10 xs11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Variables (n SRC : Z) (flags : word).
  Notation STR pc mm dtd mtl tg nbs x5 x6 x7 xa1 xa2 xa7 x28 x29 :=
    (ST pc mm (Z_to_bv 64 0x80454) x5 x6 x7 (Z_to_bv 64 DT) xa1 xa2 (Z_to_bv 64 (2147450880 + DT / 8)) (Z_to_bv 64 (mtl + 1))
        (Z_to_bv 64 tg) (Z_to_bv 64 nbs) xa7
        (Z_to_bv 64 FF) (Z_to_bv 64 r) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 18446744073709551572) (Z_to_bv 64 (FF + 32)) (Z_to_bv 64 n) (Z_to_bv 64 SRC) flags (Z_to_bv 64 (FF + 48))
        x28 x29 (Z_to_bv 64 dtd) (Z_to_bv 64 WK)).

  Ltac brk := lazymatch goal with |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) => let KB := fresh "KB" in destruct c eqn:KB end.
  Ltac wto stops := repeat (lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
        let o := eval vm_compute in (p - 0x80298) in
        let b := eval vm_compute in (existsb (Z.eqb o) stops) in lazymatch b with true => fail | false => zstep end
    | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => brk end).
  Ltac nrm255 DTM :=
    repeat (first
      [ match goal with |- context [?x mod 2^64] => rewrite (Z.mod_small x (2^64)) by lia end
      | match goal with |- context [Z.land ?x 255] =>
          replace (Z.land x 255) with (x mod 256) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; reflexivity) end
      | rewrite DTM ]).
  Ltac kbz H DTM :=
    rewrite ?AKit.zx32_lit, ?AKit.sx32_lit, ?unsigned_lit in H by lia;
    revert H; nrm255 DTM; intro H; rewrite ?Bool.negb_involutive in H;
    first [ apply Bool.negb_true_iff, Z.ltb_ge in H | apply Bool.negb_false_iff, Z.ltb_lt in H
          | apply Z.ltb_lt in H | apply Z.ltb_ge in H | idtac ].
  Ltac zb := repeat match goal with
    | H : negb _ = true |- _ => apply Bool.negb_true_iff in H
    | H : negb _ = false |- _ => apply Bool.negb_false_iff in H
    | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
    | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
    end.
  Ltac kball DTM := repeat match goal with H : context [bv_ltu] |- _ => revert H | H : context [bv_lts] |- _ => revert H | H : context [Z.ltb] |- _ => revert H end;
    unfold bv_ltu, bv_lts; rewrite ?AKit.zx32_lit, ?AKit.sx32_lit by lia; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed;
    unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); change (2 ^ (Z.of_N 64 - 1)) with (2^63);
    rewrite ?AKit.zx32_lit, ?AKit.sx32_lit, ?unsigned_lit by lia; nrm255 DTM; intros; zb.
  Ltac rz DTM := rewrite ?AKit.zx32_lit, ?AKit.sx32_lit by lia;
    repeat (first [ rewrite unsigned_lit by lia | progress nrm255 DTM ]).

  Section RESC.
  Variables (hw rank dt : list Z) (nbs tl dtd sc fl mtl tg : Z) (jA jC jD jB jE j3 j5 j6 : list byte).
  Hypothesis STATS : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis TLR : 1 <= tl.
  Hypothesis TGR : tl < tg <= 11.
  Hypothesis NBSR : 2 <= nbs <= 256.
  Hypothesis LHW : zlen hw = 256.
  Hypothesis BHW : Forall isbyte hw.
  Hypothesis LRK : zlen rank = 13.
  Hypothesis SCE : sc = tg - tl.
  Hypothesis DTLEN : zlen dt = DTB.
  Notation hwk k := (map (resc sc) (firstn (Z.to_nat k) hw) ++ skipn (Z.to_nat k) hw).
  Definition XH (hwc rk : list Z) (m1 : amem) : Prop :=
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
    /\ u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hwc)
    /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rk))
    /\ stk bsegs m1 (WK + 52) (WK + 1236) /\ stk bsegs m1 (WK + 1492) (WK + wksz) /\ stk bsegs m1 lo SPA
    /\ mem_inv bsegs m1 /\ munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 /\ wmono bsegs m5 m1
    /\ rw_cells bsegs m1 SPA (X1FRA FF DT WK jA jC jD jB jE)
    /\ rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)).
  Local Ltac open_xh I := destruct I as (DTC & HWC & RK & WS1 & WKR & STK & MI & MU & WM & FR & FFC); unfold X1FFHDR in FFC.
  Local Ltac close_xh := unfold XH, X1FFHDR; repeat (split; [eassumption|]); eassumption.

  Lemma hw_small : forall i, 0 <= i < nbs -> 0 <= Znth i hw <= tl.
  Proof.
    intros i Hi. destruct STATS as (_ & _ & FA' & _).
    assert (WSI : Znth i (firstn (Z.to_nat nbs) hw) = Znth i hw).
    { unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
    rewrite <- WSI. apply (Forall_Znth _ _ i FA'). rewrite length_firstn. lia.
  Qed.
  Lemma rank_small : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STATS as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.
  Lemma hwk_len : forall k, zlen (hwk k) = 256.
  Proof. intros k. rewrite resc_len_nat. exact LHW. Qed.
  Lemma hwk_bytes : forall k, 0 <= k <= nbs -> Forall isbyte (hwk k).
  Proof.
    intros k Hk. destruct STATS as (_ & _ & FA' & _). apply Forall_app. split.
    - replace (firstn (Z.to_nat k) hw) with (firstn (Z.to_nat k) (firstn (Z.to_nat nbs) hw)) by (rewrite firstn_firstn; f_equal; lia).
      apply Forall_map.
      eapply Forall_impl. 2: apply AProg_kit.Forall_firstnA; exact FA'. cbv beta. intros w Hw. unfold resc. destruct (Z.eqb_spec w 0); lia.
    - apply AProg_kit.Forall_skipnA. exact BHW.
  Qed.
  Lemma hwk_step : forall k, 0 <= k < 256 -> Zupd k (resc sc (Znth k hw)) (hwk k) = hwk (k + 1).
  Proof. intros k Hk. unfold Zupd, Znth. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. apply resc_step_nat. lia. Qed.

  Notation NHW := (18446744073709551615 - (WK + 1236)) (only parsing).
  Notation NW := (18446744073709551615 - WK) (only parsing).
  Lemma x1_w_bodyA : forall m1 (rk : list Z) (k : Z) xa1 x28 x29,
    XH (hwk k) rk m1 -> zlen rk = 13 -> 0 <= k < nbs ->
    (forall m2 (ya1 y28 y29 : word), k + 1 < nbs -> XH (hwk (k + 1)) rk m2 ->
       evtF bsegs RNG POST (STR 0x804cc m2 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 (k + 1)) (Z_to_bv 64 NHW) ya1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) y28 y29)) ->
    (forall m2 (ya1 y28 y29 : word), k + 1 = nbs -> XH (hwk nbs) rk m2 ->
       evtF bsegs RNG POST (STR 0x80530 m2 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 tg) ya1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x804cc m1 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 k) (Z_to_bv 64 NHW) xa1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
  Proof using HY UDT UW ART0 Hr STATS TLR TGR NBSR LHW BHW LRK SCE DTLEN.
intros until x29; intros I LRK2 HK KH KE. open_xh I.
pose proof (x1_unp_wkM _ _ _ _ _ _ _ _ _ _ HY UW m1 MU) as UW1.
destruct HY as (DT1 & DT2 & DT4 & WK1 & WK2 & WK4 & WS & KH0 & LOA & LOS & SPV1 & SPV16 & SPAB & SPA32 & DSD & WSD & DWD
                & FF64 & FF1 & FF2 & FFB & DFD & WFD & DTBk & DTR' & DTS & WKB & WKR' & WKS & FFR & LOR & RI).
pose proof atop_range as ATR.
pose proof (hw_small k ltac:(lia)) as WB.
pose proof (unpoisoned_check bsegs m1 WK (WK + wksz) (WK + 1236 + k) 1 UW1 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(clear - WK4 HK NBSR; Z.div_mod_to_equations; lia)) as (b & SHB & HB).
assert (RSH : rng RNG (shad (WK + 1236 + k)) 1).
{ apply (rng_sub' RNG (shad WK) (shspan WK wksz) (shad (WK + 1236 + k)) 1 WKS). unfold shspan. rewrite !shad_div. Z.div_mod_to_equations; lia. }
replace (shad (WK + 1236 + k)) with (Z.shiftr (WK + 1236 + k) 3 + ASHOFF) in SHB, RSH by (unfold shad; lia). unfold ASHOFF in SHB, RSH.
remember (Znth k hw) as w eqn:EW.
assert (NTHK : Znth k (hwk k) = w) by (rewrite EW; unfold Znth; apply resc_nth_nat).
assert (LHK : zlen (hwk k) = 256) by apply hwk_len.
assert (LRKB : zlen (map (Z_to_bv 8) (u32b rk)) = 52) by (rewrite length_map, u32b_length2, LRK2; reflexivity).
unfold X1FRA in FR.
assert (VW : bv_unsigned (Z_to_bv 8 w) = w) by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 8) with 256; apply Z.mod_small; lia).
pose proof (u8arr_read bsegs m1 (WK + 1236) _ k (Z_to_bv 8 w) (wa (WK + 1236 + k)) HWC
              ltac:(rewrite nth_error_map_Znth by (rewrite LHK; lia); rewrite NTHK; reflexivity) ltac:(lia) eq_refl) as RDW.
pose proof (u8arr_store_ok bsegs m1 (WK + 1236) _ k (wa (WK + 1236 + k)) HWC ltac:(rewrite length_map; lia) eq_refl) as SOK.
zstep. if_cases K0.
2: { exfalso. clear - K0 WK1 WK2 WS HK NBSR. unfold bv_ltu in K0. rewrite !Z_to_bv_unsigned in K0. unfold bv_wrap, bv_modulus in K0. change (2 ^ Z.of_N 64) with (2^64) in K0.
     apply Bool.negb_false_iff, Z.ltb_lt in K0. rewrite !Z.mod_small in K0 by lia. lia. }
clear K0. zstep. zstep. zstep. zstep. rewrite sxb_sval. zstep.
if_cases K1.
1: destruct HB as [HB0 | (HB1 & HB2)].
1: { exfalso. rewrite HB0 in K1. cbv in K1. discriminate K1. }
1: (zstep; zstep).
1: (lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:K2 end).
2: { exfalso. assert (L7 : Z.land (WK + 1236 + k) 7 = (WK + 1236 + k) mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
     assert (M8 : 0 <= (WK + 1236 + k) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
     unfold bv_lts in K2. rewrite L7 in K2. rewrite !signed_lit in K2 by (clear - M8 HB1; lia).
     zb. clear - K2 HB2. lia. }
all: try clear K1. all: try clear K2. all: try clear HB. all: try clear HB1 HB2.
all: zstep. all: zstep. all: zstep. all: zstep. all: zstep. all: zstep.
all: clear SHB RSH.
all: zstep.
all: rewrite VW.
all: (u8_store HWC k (resc sc w); [ unfold resc; destruct (Z.eqb_spec w 0) as [W0|W0];
        [ rewrite W0; reflexivity
        | replace (Z.b2z (w <? 1)) with 0 by (destruct (Z.ltb_spec w 1); [lia|reflexivity]);
          change (0 + -1) with (-1); rewrite Z.land_m1_l, land_m1_l by lia; f_equal; lia ] | ]).
all: zstep.
all: if_cases K3.
all: rewrite EW, hwk_step in HWC by lia.
all: rewrite bv_eqb_Z, !unsigned_lit in K3 by lia.
all: lazymatch goal with
     | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
         let o := eval vm_compute in (p - 524952) in
         lazymatch o with
         | 564 => apply Bool.negb_true_iff, Z.eqb_neq in K3; eapply KH; [lia | close_xh]
         | 624 => apply Bool.negb_false_iff, Z.eqb_eq in K3; zstep; zstep; zstep
         end
     end.
all: if_cases K4.
all: rewrite bv_eqb_Z, !unsigned_lit in K4 by lia.
all: lazymatch type of K4 with _ = true => exfalso; apply Z.eqb_eq in K4; lia | _ => clear K4 end.
all: zstep.
all: rewrite (zb_lxor_ones WK) by lia.
all: eapply KE; [lia | rewrite K3; close_xh].
  Qed.

  Lemma x1_w_loopA : forall (f : nat) m1 (rk : list Z) (k : Z) xa1 x28 x29,
    XH (hwk k) rk m1 -> zlen rk = 13 -> 0 <= k -> k + 1 + Z.of_nat f = nbs ->
    (forall m2 (ya1 y28 y29 : word), XH (hwk nbs) rk m2 ->
       evtF bsegs RNG POST (STR 0x80530 m2 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 tg) ya1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x804cc m1 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 k) (Z_to_bv 64 NHW) xa1 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I LRK2 HK HF KE.
    - eapply (x1_w_bodyA m1 rk k); [exact I| exact LRK2| lia| intros; exfalso; lia|].
      intros m2 ya1 y28 y29 _ I2. eapply KE; exact I2.
    - eapply (x1_w_bodyA m1 rk k); [exact I| exact LRK2| lia| | intros; exfalso; lia].
      intros m2 ya1 y28 y29 Hk I2.
      eapply (IH m2 rk (k + 1)); [exact I2| exact LRK2| lia| lia| exact KE].
  Qed.

  Lemma x1_s_bodyA : forall m1 (rk : list Z) (q t2v a7v : Z) xa1 xa2 x28 x29,
    XH (hwk nbs) rk m1 -> shifted (q + sc) sc rank rk -> 1 <= q <= tg - sc -> t2v = q + sc -> a7v = q ->
    (forall m2 (rk' : list Z) (t2v' a7v' : Z) (ya1 ya2 y28 y29 : word), 1 < q ->
       XH (hwk nbs) rk' m2 -> shifted (q - 1 + sc) sc rank rk' -> t2v' = q - 1 + sc -> a7v' = q - 1 ->
       evtF bsegs RNG POST (STR 0x80530 m2 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 t2v') ya1 ya2 (Z_to_bv 64 a7v') y28 y29)) ->
    (forall m2 (rk' : list Z) (y7 ya1 ya2 ya7 y28 y29 : word), q = 1 ->
       XH (hwk nbs) rk' m2 -> shifted sc sc rank rk' ->
       evtF bsegs RNG POST (STR 0x805d4 m2 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) y7 ya1 ya2 ya7 y28 y29)) ->
    evtF bsegs RNG POST (STR 0x80530 m1 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 t2v) xa1 xa2 (Z_to_bv 64 a7v) x28 x29).
  Proof using HY UDT UW ART0 Hr STATS TLR TGR NBSR LHW BHW LRK SCE DTLEN.
intros until x29; intros I SH HQ E2 E7 KH KE. subst t2v a7v.
assert (HLE4 : forall x, 0 <= x < 2^32 -> le4 (Z_to_bv 64 x) = map (Z_to_bv 8) (u32q x)).
{ intros x Hx. unfold le4, u32q. cbn [Z_to_le_bytes map]. rewrite Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64). rewrite (Z.mod_small x) by lia.
  rewrite !Z.shiftr_shiftr by lia. rewrite !Z.shiftr_div_pow2 by lia. cbn [Z.add Pos.add Pos.succ].
  change (2^8) with 256. change (2^16) with 65536. change (2^24) with 16777216.
  f_equal; [|f_equal; [|f_equal; [|f_equal]]]; apply Z_to_bv8_mod; change (2^8) with 256; Z.div_mod_to_equations; lia. }
assert (HSPL : forall (ws : list Z) i, 0 <= i < zlen ws -> exists pre post, ws = pre ++ Znth i ws :: post /\ length pre = Z.to_nat i).
{ intros ws i Hi. destruct (nth_error_split (map (fun z : Z => z) ws) (Z.to_nat i) (Znth i ws) (nth_error_map_Znth (fun z : Z => z) ws i Hi)) as (pre & post & E & Hlen).
  rewrite map_id in E. exists pre, post. split; assumption. }
assert (HUPD : forall (a b : list Z) y w, upd_nat (length a) w (a ++ y :: b) = a ++ w :: b).
{ intros a. induction a as [|h a IH]; intros b y w; cbn; [reflexivity|]. rewrite IH. reflexivity. }
destruct I as (DTC & HWC & RK & WS1 & WKR & STK & MI & MU & WM & FR & FFC).
pose proof HY as HY'. unfold x1A_hyps in HY'.
destruct HY' as (DT1 & DT2 & DT4 & WK1 & WK2 & WK4 & WS & _ & _ & LOS & SPV1 & _ & SPAB & _ & _ & WSD & DWD
                & _ & FF1 & FF2 & _ & _ & WFD & _ & _ & _ & _ & WKR' & WKS & _ & _ & _).
pose proof SH as (LRK2 & _). unfold FseNCount.Zlength in LRK2.
assert (SCB : 1 <= sc <= 10) by lia.
assert (QB : 1 <= q <= 10) by lia.
assert (QSB : 2 <= q + sc <= 11) by lia.
destruct (shifted_step (q + sc) sc rank rk SH ltac:(lia) ltac:(lia)) as [ERD SH'].
replace (q + sc - sc) with q in ERD, SH' by lia.
pose proof (rank_small q ltac:(lia)) as VB.
set (v := Znth q rank) in *. clearbody v.
assert (LRKB : zlen (map (Z_to_bv 8) (u32b rk)) = 52) by (rewrite length_map, u32b_length2, LRK2; reflexivity).
assert (LHK : zlen (map (Z_to_bv 8) (hwk nbs)) = 256) by (rewrite length_map; apply hwk_len).
assert (LDT : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; exact DTLEN).
assert (RD1 : ov_read_bytes bsegs m1 (wa (WK + 4 * q)) 4 = Some (le4 (Z_to_bv 64 v))).
{ destruct (HSPL rk q ltac:(lia)) as (pre & post & Erk & Lpre).
  destruct RK as (BA & _). rewrite Erk, u32b_app, map_app in BA. apply bytes_at_app in BA. destruct BA as (_ & BA).
  cbn [u32b] in BA. rewrite map_app in BA. apply bytes_at_app in BA. destruct BA as (BA & _).
  rewrite length_map, u32b_length, Lpre in BA. replace (WK + Z.of_nat (4 * Z.to_nat q)) with (WK + 4 * q) in BA by lia.
  pose proof (ov_read_of_bytes_at bsegs m1 _ _ BA) as R. rewrite length_map in R. cbn [u32q length] in R.
  rewrite HLE4 by lia. rewrite <- ERD. exact R. }
pose proof (u8arr_store_ok_n bsegs m1 WK _ (4 * (q + sc)) 4 (wa (WK + 4 * (q + sc))) RK ltac:(lia) ltac:(rewrite LRKB; lia) eq_refl) as SOK.
assert (RKn : u8arr bsegs (write_to_mem m1 (wa (WK + 4 * (q + sc))) (le4 (Z_to_bv 64 v))) WK (map (Z_to_bv 8) (u32b (Zupd (q + sc) v rk)))).
{ destruct (HSPL rk (q + sc) ltac:(lia)) as (pre & post & Erk & Lpre).
  pose proof (u8arr_write_bytes bsegs m1 WK _ (4 * (q + sc)) (le4 (Z_to_bv 64 v)) RK ltac:(lia) ltac:(rewrite length_le4, length_map, u32b_length; lia)) as W.
  replace (upd_bytes _ _ _) with (map (Z_to_bv 8) (u32b (Zupd (q + sc) v rk))) in W; [exact W|].
  rewrite Erk. unfold Zupd. rewrite <- Lpre. rewrite HUPD. rewrite !u32b_app, !map_app. cbn [u32b]. rewrite !map_app.
  replace (Z.to_nat (4 * (q + sc))) with (length (map (Z_to_bv 8) (u32b pre))) by (rewrite length_map, u32b_length; lia).
  rewrite upd_bytes_mid by (rewrite length_le4, length_map; reflexivity). rewrite HLE4 by lia. reflexivity. }
pose proof (x1_unp_wkM RNG m5 SPV SPA lo DT DTB WK wksz FF HY UW m1 MU) as UWm.
pose proof (unpoisoned_check bsegs m1 WK (WK + wksz) (WK + 4 * q) 4 UWm ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(clear - WK4; Z.div_mod_to_equations; lia)) as (b1 & SB1 & HB1).
pose proof (unpoisoned_check bsegs m1 WK (WK + wksz) (WK + 4 * (q + sc)) 4 UWm ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(clear - WK4; Z.div_mod_to_equations; lia)) as (b2 & SB2 & HB2).
assert (RSH1 : rng RNG (shad (WK + 4 * q)) 1)
  by (apply (rng_sub' RNG (shad WK) (shspan WK wksz) _ 1 WKS); unfold shspan; rewrite !shad_div; Z.div_mod_to_equations; lia).
assert (RSH2 : rng RNG (shad (WK + 4 * (q + sc))) 1)
  by (apply (rng_sub' RNG (shad WK) (shspan WK wksz) _ 1 WKS); unfold shspan; rewrite !shad_div; Z.div_mod_to_equations; lia).
replace (shad (WK + 4 * q)) with (Z.shiftr (WK + 4 * q) 3 + 2147450880) in SB1, RSH1 by (unfold shad, ASHOFF; lia).
replace (shad (WK + 4 * (q + sc))) with (Z.shiftr (WK + 4 * (q + sc)) 3 + 2147450880) in SB2, RSH2 by (unfold shad, ASHOFF; lia).
clear WKS UWm.
zstep.
zstep.
setreg 12 (Z_to_bv 64 (4 * q)) ltac:(first [ reflexivity | f_equal; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; repeat match goal with |- context [Z.land ?x ?c] => is_Zlit c; let k := eval vm_compute in (Z.log2 (c + 1)) in replace (Z.land x c) with (x mod 2 ^ k) by (change c with (Z.ones k); rewrite Z.land_ones by lia; reflexivity) end; repeat match goal with |- context [2 ^ ?k] => is_Zlit k; let p := eval vm_compute in (2 ^ k) in change (2 ^ k) with p end; first [ lia | Z.div_mod_to_equations; lia ] ]).
zstep.
if_cases K1.
2: { exfalso. revert K1; unfold bv_ltu, bv_lts, bv_eqb; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed; unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); change (2 ^ (Z.of_N 64 - 1)) with (2^63); intro K1; zb. rewrite !Z.mod_small in K1 by lia. lia. }
zstep.
zstep.
setreg 28 (Z_to_bv 64 (4 * (q + sc))) ltac:(first [ reflexivity | f_equal; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; repeat match goal with |- context [Z.land ?x ?c] => is_Zlit c; let k := eval vm_compute in (Z.log2 (c + 1)) in replace (Z.land x c) with (x mod 2 ^ k) by (change c with (Z.ones k); rewrite Z.land_ones by lia; reflexivity) end; repeat match goal with |- context [2 ^ ?k] => is_Zlit k; let p := eval vm_compute in (2 ^ k) in change (2 ^ k) with p end; first [ lia | Z.div_mod_to_equations; lia ] ]).
zstep.
if_cases K2.
2: { exfalso. revert K2; unfold bv_ltu, bv_lts, bv_eqb; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed; unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); change (2 ^ (Z.of_N 64 - 1)) with (2^63); intro K2; zb. rewrite !Z.mod_small in K2 by lia. lia. }
zstep.
zstep.
zstep.
setreg 11 (Z_to_bv 64 (WK + 4 * q)) ltac:(first [ reflexivity | f_equal; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; repeat match goal with |- context [Z.land ?x ?c] => is_Zlit c; let k := eval vm_compute in (Z.log2 (c + 1)) in replace (Z.land x c) with (x mod 2 ^ k) by (change c with (Z.ones k); rewrite Z.land_ones by lia; reflexivity) end; repeat match goal with |- context [2 ^ ?k] => is_Zlit k; let p := eval vm_compute in (2 ^ k) in change (2 ^ k) with p end; first [ lia | Z.div_mod_to_equations; lia ] ]).
zstep.
zstep.
zstep.
zstep.
rewrite sxb_sval.
if_cases K3.
1: destruct HB1 as [HB0 | (HB1a & HB1b)].
1: { exfalso. rewrite HB0 in K3. cbv in K3. discriminate K3. }
1: (zstep; zstep; zstep).
1: if_cases K4.
2: { exfalso. assert (L7 : Z.land (WK + 4 * q) 7 = (WK + 4 * q) mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
     assert (M8 : 0 <= (WK + 4 * q) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
     unfold bv_lts in K4. rewrite L7 in K4. rewrite !signed_lit in K4 by (clear - M8 HB1a; lia).
     zb. clear - K4 HB1b. lia. }
all: zstep.
all: zstep.
all: zstep.
all: setreg 12 (Z_to_bv 64 (WK + 4 * (q + sc))) ltac:(first [ reflexivity | f_equal; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; repeat match goal with |- context [Z.land ?x ?c] => is_Zlit c; let k := eval vm_compute in (Z.log2 (c + 1)) in replace (Z.land x c) with (x mod 2 ^ k) by (change c with (Z.ones k); rewrite Z.land_ones by lia; reflexivity) end; repeat match goal with |- context [2 ^ ?k] => is_Zlit k; let p := eval vm_compute in (2 ^ k) in change (2 ^ k) with p end; first [ lia | Z.div_mod_to_equations; lia ] ]).
all: zstep.
all: zstep.
all: zstep.
all: zstep.
all: setreg 11 (Z_to_bv 64 v) ltac:(symmetry; apply AKit.sx32_lit; lia).
all: rewrite sxb_sval.
all: zstep.
all: if_cases K5.
all: lazymatch type of K5 with
  | negb (bv_eqb _ _) = true =>
      destruct HB2 as [HB0 | (HB2a & HB2b)];
      [ exfalso; rewrite HB0 in K5; cbv in K5; discriminate K5
      | zstep; zstep; zstep; if_cases K6;
        [ idtac
        | exfalso; assert (L7 : Z.land (WK + 4 * (q + sc)) 7 = (WK + 4 * (q + sc)) mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity);
          assert (M8 : 0 <= (WK + 4 * (q + sc)) mod 8 < 8) by (apply Z.mod_pos_bound; lia);
          unfold bv_lts in K6; rewrite L7 in K6; rewrite !signed_lit in K6 by (clear - M8 HB2a; lia); zb; clear - K6 HB2b; lia ] ]
  | _ => idtac end.
all: zstep.
all: change (Z_to_bv 64 (WK + 4 * (q + sc))) with (wa (WK + 4 * (q + sc))).
all: clear RK SB1 SB2 RD1 RSH1 RSH2.
all: apply (mem_inv_store bsegs m1 (wa (WK + 4 * (q + sc))) (le4 (Z_to_bv 64 v))) in MI; [|rewrite length_le4; exact SOK].
all: clear SOK.
all: apply (u8arr_frame bsegs m1 DT _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in DTC; [|lia|rewrite length_le4; lia|rewrite length_le4, LDT; lia].
all: apply (u8arr_frame bsegs m1 (WK + 1236) _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in HWC; [|lia|rewrite length_le4; lia|rewrite length_le4, LHK; lia].
all: apply (stk_write bsegs m1 _ _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in WS1; [|lia|rewrite length_le4; lia].
all: apply (stk_write bsegs m1 _ _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in WKR; [|lia|rewrite length_le4; lia].
all: apply (stk_write bsegs m1 _ _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in STK; [|lia|rewrite length_le4; lia].
all: apply (munch_write _ m5 m1 (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in MU; [|lia|rewrite length_le4; lia|cbn [inside]; rewrite length_le4; lia].
all: apply (wmono_write bsegs m5 m1 (wa (WK + 4 * (q + sc))) (le4 (Z_to_bv 64 v))) in WM.
all: apply (rw_cells_frame bsegs m1 SPA _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in FR; [|lia|rewrite length_le4; lia|unfold X1FRA; cbn [cells_size csize Nat.add]; rewrite length_le4; lia].
all: apply (rw_cells_frame bsegs m1 FF _ (WK + 4 * (q + sc)) (le4 (Z_to_bv 64 v))) in FFC; [|lia|rewrite length_le4; lia|unfold X1FFHDR; cbn [cells_size csize Nat.add]; rewrite length_le4; lia].
all: remember (write_to_mem m1 (wa (WK + 4 * (q + sc))) (le4 (Z_to_bv 64 v))) as m2 eqn:EM.
all: clear EM.
all: zstep.
all: zstep.
all: zstep.
all: setreg 7 (Z_to_bv 64 (q - 1 + sc)) ltac:(f_equal; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2^32); change (2 ^ (Z.of_N 32 - 1)) with (2^31); rewrite Z.mod_small by lia; lia).
all: setreg 17 (Z_to_bv 64 (q - 1)) ltac:(f_equal; lia).
all: replace (q + sc - 1) with (q - 1 + sc) in SH' by lia.
all: if_cases K7.
all: revert K7; unfold bv_ltu, bv_lts, bv_eqb; rewrite ?Z_to_bv_unsigned, ?Z_to_bv_signed; unfold bv_wrap, bv_swrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 64) with (2^64); change (2 ^ (Z.of_N 64 - 1)) with (2^63); intro K7; zb.
all: rewrite ?Z.mod_small in K7 by lia.
all: lazymatch type of K7 with
  | _ < _ =>
      eapply (KH m2 (Zupd (q + sc) v rk)); [lia | unfold XH; repeat (split; [eassumption|]); eassumption | exact SH' | reflexivity | reflexivity]
  | _ =>
      assert (Q1 : q = 1) by lia; zstep; subst q; replace (1 - 1 + sc) with sc in SH' by lia;
      eapply (KE m2 (Zupd (1 + sc) v rk)); [reflexivity | unfold XH; repeat (split; [eassumption|]); eassumption | exact SH']
  end.
  Qed.

  Lemma x1_s_loopA : forall (f : nat) m1 (rk : list Z) (q t2v a7v : Z) xa1 xa2 x28 x29,
    XH (hwk nbs) rk m1 -> shifted (q + sc) sc rank rk -> 1 <= q <= tg - sc -> q = 1 + Z.of_nat f -> t2v = q + sc -> a7v = q ->
    (forall m2 (rk' : list Z) (y7 ya1 ya2 ya7 y28 y29 : word),
       XH (hwk nbs) rk' m2 -> shifted sc sc rank rk' ->
       evtF bsegs RNG POST (STR 0x805d4 m2 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) y7 ya1 ya2 ya7 y28 y29)) ->
    evtF bsegs RNG POST (STR 0x80530 m1 dtd mtl tg nbs (Z_to_bv 64 sc) (Z_to_bv 64 NW) (Z_to_bv 64 t2v) xa1 xa2 (Z_to_bv 64 a7v) x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I SH HQ HF E2 E7 KE.
    - eapply (x1_s_bodyA m1 rk q); [exact I| exact SH| exact HQ| exact E2| exact E7| intros; exfalso; lia|].
      intros m2 rk' y7 ya1 ya2 ya7 y28 y29 _ I2 SH2. eapply KE; [exact I2| exact SH2].
    - eapply (x1_s_bodyA m1 rk q); [exact I| exact SH| exact HQ| exact E2| exact E7| | intros; exfalso; lia].
      intros m2 rk' t2v' a7v' ya1 ya2 y28 y29 Hq I2 SH2 E2' E7'.
      eapply (IH m2 rk' (q - 1)); [exact I2| exact SH2| lia| lia| exact E2'| exact E7'| exact KE].
  Qed.

  Lemma x1_z_bodyA : forall m1 (rk0 rk : list Z) (z : Z) x7 xa1 xa2 xa7 x28 x29,
    XH (hwk nbs) rk m1 -> zeroed z sc rk0 rk -> 1 <= z <= sc ->
    (forall m2 (rk' : list Z) (ya1 ya2 ya7 y28 y29 : word), 1 <= z - 1 ->
       XH (hwk nbs) rk' m2 -> zeroed (z - 1) sc rk0 rk' ->
       evtF bsegs RNG POST (STR 0x805d4 m2 dtd mtl tg nbs (Z_to_bv 64 (z - 1)) (Z_to_bv 64 NW) x7 ya1 ya2 ya7 y28 y29)) ->
    (forall m2 (rk' : list Z) (ya1 ya2 y28 y29 : word), z - 1 = 0 ->
       XH (hwk nbs) rk' m2 -> zeroed 0 sc rk0 rk' ->
       evtF bsegs RNG POST (STR 0x80610 m2 dtd mtl tg nbs (Z_to_bv 64 0) (Z_to_bv 64 NW) x7 ya1 ya2 (Z_to_bv 64 tg) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x805d4 m1 dtd mtl tg nbs (Z_to_bv 64 z) (Z_to_bv 64 NW) x7 xa1 xa2 xa7 x28 x29).
  Proof using HY UDT UW ART0 Hr STATS TLR TGR NBSR LHW BHW LRK SCE DTLEN.
    intros until x29; intros I ZE HZ KH KE. open_xh I.
    pose proof ZE as (LRK2 & ZEF).
    assert (UPDW : upd_bytes (map (Z_to_bv 8) (u32b rk)) (Z.to_nat (4 * z)) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]
                   = map (Z_to_bv 8) (u32b (Zupd z 0 rk))).
    { assert (ZI : 0 <= z < zlen rk) by (rewrite LRK2; clear - HZ TGR TLR SCE; lia).
      destruct (nth_error_split (map (fun z : Z => z) rk) (Z.to_nat z) (Znth z rk) (nth_error_map_Znth (fun z : Z => z) rk z ZI)) as (pre & post & E & Hlen).
      rewrite map_id in E. unfold Zupd. rewrite E. rewrite <- Hlen.
      assert (UPD : forall (a b : list Z) y v, upd_nat (length a) v (a ++ y :: b) = a ++ v :: b).
      { intros a. induction a as [|h a IH]; intros b y v; cbn; [reflexivity|]. rewrite IH. reflexivity. }
      rewrite UPD. rewrite !u32b_app. cbn [u32b]. rewrite !map_app.
      replace (Z.to_nat (4 * z)) with (length (map (Z_to_bv 8) (u32b pre))) by (rewrite length_map, u32b_length; lia).
      rewrite upd_bytes_mid by (rewrite length_map; reflexivity). reflexivity. }
    pose proof (x1_unp_wkM RNG m5 SPV SPA lo DT DTB WK wksz FF HY UW m1 MU) as UWm.
    pose proof HY as HY'.
    destruct HY' as (DT1 & DT2 & DT4 & WK1 & WK2 & WK4 & WS & KH0 & LOA & LOS & SPV1 & SPV16 & SPAB & SPA32 & DSD & WSD & DWD
                    & FF64 & FF1 & FF2 & FFB & DFD & WFD & DTBk & DTR' & DTS & WKB & WKR' & WKS & FFR & LOR & RI).
    pose proof (unpoisoned_check bsegs m1 WK (WK + wksz) (WK + 4 * z) 4 UWm ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(clear - WK4 HZ; Z.div_mod_to_equations; lia)) as (b & SHB & HB).
    assert (SH4 : forall M, M = 2^64 - 1 -> Z.shiftr (Z.land (Z.shiftl z 32) M) 30 = 4 * z).
    { intros M ->. change (2^64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
       rewrite Z.mod_small by lia. replace (z * 2^32) with ((4 * z) * 2^30) by lia. rewrite Z.div_mul by lia. reflexivity. }
    assert (LZ : forall M, M = 2^32 - 1 -> Z.land z M = z).
    { intros M ->. change (2^32 - 1) with (Z.ones 32). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
    zstep. zstep. zstep.
    lazymatch goal with |- context [Z.shiftr (Z.land (Z.shiftl z 32) ?M) 30] => rewrite (SH4 M) by reflexivity end.
    if_cases K0.
    2: { exfalso. unfold bv_ltu in K0. rewrite !Z_to_bv_unsigned in K0. unfold bv_wrap, bv_modulus in K0.
          change (2 ^ Z.of_N 64) with (2^64) in K0. rewrite !Z.mod_small in K0 by lia. apply Bool.negb_false_iff, Z.ltb_lt in K0. lia. }
    clear K0. zstep. zstep. zstep.
    lazymatch goal with |- context [Z.land z ?M] => rewrite (LZ M) by reflexivity end.
    setreg 11 (Z_to_bv 64 (WK + 4 * z)) ltac:(f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
    assert (RSH : rng RNG (shad (WK + 4 * z)) 1)
      by (apply (rng_sub' RNG (shad WK) (shspan WK wksz) (shad (WK + 4 * z)) 1 WKS); unfold shspan, shad; rewrite !Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    replace (shad (WK + 4 * z)) with (Z.shiftr (WK + 4 * z) 3 + ASHOFF) in SHB, RSH by (unfold shad; lia).
    unfold ASHOFF in SHB, RSH.
    zstep. zstep.
    zstep. rewrite ?sxb_sval.
    zstep.
    if_cases K1.
    1: destruct HB as [HB0 | (HB1 & HB2)].
    1: { exfalso. rewrite HB0 in K1. cbv in K1. discriminate K1. }
    1: (zstep; zstep).
    1: zstep.
    1: (lazymatch goal with |- context [if ?c then _ else _] => destruct c eqn:K2 end).
    2: { exfalso. assert (L7 : Z.land (WK + 4 * z) 7 = (WK + 4 * z) mod 8) by (change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity).
         assert (M8 : 0 <= (WK + 4 * z) mod 8 < 8) by (apply Z.mod_pos_bound; lia).
         unfold bv_lts in K2. rewrite L7 in K2. rewrite !signed_lit in K2 by (clear - M8 HB1; lia).
         apply Z.ltb_ge in K2. clear - K2 HB2. lia. }
    all: zstep.
    all: assert (LDT : zlen (map (Z_to_bv 8) dt) = DTB) by (rewrite length_map; exact DTLEN).
    all: assert (LHK : zlen (map (Z_to_bv 8) (hwk nbs)) = 256) by (rewrite length_map; apply hwk_len).
    all: assert (LRB : zlen (map (Z_to_bv 8) (u32b rk)) = 52) by (rewrite length_map, u32b_length2, LRK2; reflexivity).
    all: pose proof (u8arr_store_ok_n bsegs _ WK _ (4 * z) 4 (wa (WK + 4 * z)) RK ltac:(lia) ltac:(rewrite LRB; lia) eq_refl) as SOK.
    all: zstep.
    all: pose proof (le4_bcast 0 ltac:(lia)) as L4; rewrite Z.mul_0_l in L4; rewrite L4; clear L4.
    all: cbn [repeat].
    all: unfold X1FRA in FR.
    all: assert (SWSA : WK + wksz <= SPA \/ SPA + 216 <= WK) by (clear - WSD LOS SPAB; lia).
    all: pose proof (u8arr_write_bytes bsegs _ WK _ (4 * z) [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0] RK ltac:(lia) ltac:(cbn [length]; rewrite length_map, u32b_length; lia)) as ARR2.
    all: clear RK; store_done; rename ARR2 into RK.
    all: assert (SW1 : bv_swrap 32 (z + -1) = z - 1) by (unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; change (2 ^ Z.of_N 32) with (2^32); change (2 ^ (Z.of_N 32 - 1)) with (2^31); rewrite Z.mod_small by lia; lia).
    all: rewrite !SW1.
    all: zstep.
    all: if_cases K3.
    all: rewrite bv_eqb_Z, !Z_to_bv_unsigned in K3; unfold bv_wrap, bv_modulus in K3; change (2 ^ Z.of_N 64) with (2^64) in K3; rewrite !Z.mod_small in K3 by lia.
    all: rewrite UPDW in RK.
    all: pose proof (zeroed_step z sc rk0 rk ZE ltac:(lia) ltac:(lia)) as ZE'.
    1,3: (eapply KH; [lia | unfold XH, X1FFHDR, X1FRA; repeat (split; [eassumption|]); eassumption | exact ZE']).
    all: assert (EZ : z - 1 = 0) by lia; rewrite EZ in ZE'.
    all: zstep.
    all: rewrite EZ.
    all: (eapply KE; [exact EZ | unfold XH, X1FFHDR, X1FRA; repeat (split; [eassumption|]); eassumption | exact ZE']).
  Qed.

  Lemma x1_z_loopA : forall (f : nat) m1 (rk0 rk : list Z) (z : Z) x7 xa1 xa2 xa7 x28 x29,
    XH (hwk nbs) rk m1 -> zeroed z sc rk0 rk -> 1 <= z <= sc -> z = 1 + Z.of_nat f ->
    (forall m2 (rk' : list Z) (ya1 ya2 y28 y29 : word),
       XH (hwk nbs) rk' m2 -> zeroed 0 sc rk0 rk' ->
       evtF bsegs RNG POST (STR 0x80610 m2 dtd mtl tg nbs (Z_to_bv 64 0) (Z_to_bv 64 NW) x7 ya1 ya2 (Z_to_bv 64 tg) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x805d4 m1 dtd mtl tg nbs (Z_to_bv 64 z) (Z_to_bv 64 NW) x7 xa1 xa2 xa7 x28 x29).
  Proof.
    induction f as [|f IH]; intros until x29; intros I ZE HZ HF KE.
    - eapply (x1_z_bodyA m1 rk0 rk z); [exact I| exact ZE| exact HZ| intros; exfalso; lia|].
      intros m2 rk' ya1 ya2 y28 y29 _ I2 ZE2. eapply KE; [exact I2| exact ZE2].
    - eapply (x1_z_bodyA m1 rk0 rk z); [exact I| exact ZE| exact HZ| | intros; exfalso; lia].
      intros m2 rk' ya1 ya2 ya7 y28 y29 Hz I2 ZE2.
      eapply (IH m2 rk0 rk' (z - 1)); [exact I2| exact ZE2| lia| lia| exact KE].
  Qed.

  End RESC.

  Lemma x1_h2A : forall m1 (hw rank dt : list Z) (nbs tl mtl : Z) (fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 x28 x29 : word) (dtd : Z),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= mtl <= 12 -> 1 <= tl < Z.min (mtl + 1) 11 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw -> zlen rank = 13 ->
    mem_inv bsegs m1 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 -> stk bsegs m1 lo SPA ->
    rw_cells bsegs m1 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = DTB ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    stk bsegs m1 (WK + 52) (WK + 1236) -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    (forall m2 (hw' rank' : list Z) (y5 y6 y7 ya1 ya2 y28 y29 : word),
       huf_stats_ok (firstn (Z.to_nat nbs) hw') rank' (Z.min (mtl + 1) 11) -> zlen hw' = 256 -> Forall isbyte hw' -> zlen rank' = 13 ->
       mem_inv bsegs m2 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m2 -> wmono bsegs m5 m2 -> stk bsegs m2 lo SPA ->
       rw_cells bsegs m2 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       u8arr bsegs m2 DT (map (Z_to_bv 8) dt) ->
       u8arr bsegs m2 (WK + 1236) (map (Z_to_bv 8) hw') -> u8arr bsegs m2 WK (map (Z_to_bv 8) (u32b rank')) ->
       stk bsegs m2 (WK + 52) (WK + 1236) -> stk bsegs m2 (WK + 1492) (WK + wksz) ->
       evtF bsegs RNG POST (STR 0x80610 m2 dtd mtl (Z.min (mtl + 1) 11) nbs y5 y6 y7 ya1 ya2 (Z_to_bv 64 (Z.min (mtl + 1) 11)) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x804bc m1 dtd mtl (Z.min (mtl + 1) 11) nbs x5 x6 x7 (Z_to_bv 64 mtl) (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
  Proof.
    intros until dtd; intros STATS MTL TLR NBSR LHW BHW LRK MI MU WM STK FR FFC DTC DTLEN HWC RK WS1 WKR KK.
    set (tg := Z.min (mtl + 1) 11) in *.
    assert (TG11 : tg <= 11) by (unfold tg; lia).
    assert (WKB0 : 0 <= WK + 1236 < 2^64)
      by (pose proof HY as H; unfold x1A_hyps in H; destruct H as (_ & _ & _ & W1 & W2 & _ & W3 & _); lia).
    zstep. rewrite (swrap32_small (tg - tl)) by lia.
    zstep. if_cases K0.
    1: { exfalso. rewrite bv_eqb_Z, !unsigned_lit in K0 by lia. apply Z.eqb_eq in K0. lia. }
    clear K0. zstep. zstep.
    lazymatch goal with |- evtF _ _ _ ?S =>
      let a1v := StepF.reg_val 11 in
      replace S with (STR 0x804cc m1 dtd mtl tg nbs (Z_to_bv 64 (tg - tl)) (Z_to_bv 64 0) (Z_to_bv 64 (18446744073709551615 - (WK + 1236)))
                        a1v (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29)
        by (cbv [mkR]; repeat f_equal; first [reflexivity | symmetry; apply zb_lxor_ones; exact WKB0 | lia]) end.
    eapply (x1_w_loopA hw rank dt nbs tl dtd (tg - tl) fl mtl tg jA jC jD jB jE j3 j5 j6 STATS ltac:(lia) ltac:(lia) NBSR LHW BHW LRK eq_refl DTLEN
              (Z.to_nat (nbs - 1)) m1 rank 0);
      [ unfold XH; cbn [Z.to_nat firstn skipn map app]; repeat (split; [eassumption|]); eassumption
      | exact LRK | lia | lia |].
    intros m2 ya1 y28 y29 I2.
    pose proof STATS as (T1 & T2 & T3 & T4 & T5 & T6).
    assert (HI : forall v, tl < v <= 12 -> Znth v rank = 0).
    { intros v Hv. rewrite (T5 v) by lia. unfold hcount. rewrite (proj1 (count_occ_not_In Z.eq_dec (firstn (Z.to_nat nbs) hw) v)); [reflexivity|].
      intros IN. pose proof (proj1 (Forall_forall _ _) T3 v IN) as HX. cbv beta in HX. lia. }
    eapply (x1_s_loopA hw rank dt nbs tl dtd (tg - tl) fl mtl tg jA jC jD jB jE j3 j5 j6 STATS ltac:(lia) ltac:(lia) NBSR LHW BHW LRK eq_refl DTLEN
              (Z.to_nat (tl - 1)) m2 rank tl tg tl);
      [ exact I2
      | replace (tl + (tg - tl)) with tg by lia; apply (shifted_init_tg tg (tg - tl) tl rank T4 ltac:(lia) ltac:(lia) TG11 HI)
      | lia | lia | lia | reflexivity |].
    intros m3 rk' z7 za1 za2 za7 z28 z29 I3 SH3.
    assert (CL3 : zlen rk' = 13) by (destruct SH3 as (L & _); exact L).
    eapply (x1_z_loopA hw rank dt nbs tl dtd (tg - tl) fl mtl tg jA jC jD jB jE j3 j5 j6 STATS ltac:(lia) ltac:(lia) NBSR LHW BHW LRK eq_refl DTLEN
              (Z.to_nat (tg - tl - 1)) m3 rk' rk' (tg - tl));
      [ exact I3 | apply zeroed_init; exact CL3 | lia | lia |].
    intros m4 rk'' wa1 wa2 w28 w29 I4 ZE4.
    destruct I4 as (DTC4 & HWC4 & RK4 & WS14 & WKR4 & STK4 & MI4 & MU4 & WM4 & FR4 & FFC4).
    pose proof (zeroed_resc (tg - tl) rank rk' rk'' tl SH3 ZE4 ltac:(lia) ltac:(lia) ltac:(lia) HI) as RR4.
    assert (EFH : firstn (Z.to_nat nbs) (map (resc (tg - tl)) (firstn (Z.to_nat nbs) hw) ++ skipn (Z.to_nat nbs) hw) = map (resc (tg - tl)) (firstn (Z.to_nat nbs) hw)).
    { assert (LL : length (map (resc (tg - tl)) (firstn (Z.to_nat nbs) hw)) = Z.to_nat nbs) by (rewrite length_map, length_firstn; lia).
      rewrite firstn_app, LL, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- LL at 1. apply firstn_all. }
    eapply KK; [| | | | exact MI4| exact MU4| exact WM4| exact STK4| exact FR4| exact FFC4| exact DTC4| exact HWC4| exact RK4| exact WS14| exact WKR4].
    - rewrite EFH. pose proof (huf_stats_rescale _ rank rk'' tl (tg - tl) STATS ltac:(lia) ltac:(lia) RR4) as HS.
      replace (tl + (tg - tl)) with tg in HS by lia. exact HS.
    - apply (hwk_len hw (tg - tl) LHW).
    - apply (hwk_bytes hw rank dt nbs tl (tg - tl) tg STATS ltac:(lia) NBSR BHW eq_refl nbs); lia.
    - destruct RR4 as [RL _]. exact RL.
  Qed.

  Definition x1_h2A_stmt : Prop := forall m1 (hw rank dt : list Z) (nbs tl mtl : Z) (fl : Z) (jA jC jD jB jE j3 j5 j6 : list byte)
      (x5 x6 x7 x28 x29 : word) (dtd : Z),
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= mtl <= 12 -> 1 <= tl < Z.min (mtl + 1) 11 -> 2 <= nbs <= 256 -> zlen hw = 256 -> Forall isbyte hw -> zlen rank = 13 ->
    mem_inv bsegs m1 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 -> wmono bsegs m5 m1 -> stk bsegs m1 lo SPA ->
    rw_cells bsegs m1 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m1 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) -> zlen dt = DTB ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) -> u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    stk bsegs m1 (WK + 52) (WK + 1236) -> stk bsegs m1 (WK + 1492) (WK + wksz) ->
    (forall m2 (hw' rank' : list Z) (y5 y6 y7 ya1 ya2 y28 y29 : word),
       huf_stats_ok (firstn (Z.to_nat nbs) hw') rank' (Z.min (mtl + 1) 11) -> zlen hw' = 256 -> Forall isbyte hw' -> zlen rank' = 13 ->
       mem_inv bsegs m2 -> munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m2 -> wmono bsegs m5 m2 -> stk bsegs m2 lo SPA ->
       rw_cells bsegs m2 SPA (X1FRA FF DT WK jA jC jD jB jE) -> rw_cells bsegs m2 FF (X1FFHDR fl j3 j5 j6 (Z_to_bv 64 tl) (Z_to_bv 64 nbs)) ->
       u8arr bsegs m2 DT (map (Z_to_bv 8) dt) ->
       u8arr bsegs m2 (WK + 1236) (map (Z_to_bv 8) hw') -> u8arr bsegs m2 WK (map (Z_to_bv 8) (u32b rank')) ->
       stk bsegs m2 (WK + 52) (WK + 1236) -> stk bsegs m2 (WK + 1492) (WK + wksz) ->
       evtF bsegs RNG POST (STR 0x80610 m2 dtd mtl (Z.min (mtl + 1) 11) nbs y5 y6 y7 ya1 ya2 (Z_to_bv 64 (Z.min (mtl + 1) 11)) y28 y29)) ->
    evtF bsegs RNG POST (STR 0x804bc m1 dtd mtl (Z.min (mtl + 1) 11) nbs x5 x6 x7 (Z_to_bv 64 mtl) (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x28 x29).
End X1B.
End CANSEC1.
