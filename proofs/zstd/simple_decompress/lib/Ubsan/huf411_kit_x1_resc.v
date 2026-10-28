(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit huf411_kit_x1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV n DT WK wksz lo : Z).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis NR : n < 2^32.
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis WK1492 : 1492 <= wksz.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Variables (flags : word) (f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f104 f112 f120 : list byte).
  Variables (hw rank : list Z) (nbs tl r0 : Z).
  Hypothesis STOK : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBR : 2 <= nbs <= 256.  Hypothesis R0R : 1 <= r0 <= n.
  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis HWBY : Forall isbyte hw.  Hypothesis RKLEN : Z.of_nat (length rank) = 13.
  Notation X1S fl wn wt dt rst syb m1 := (x1s DT WK wksz SPV lo m SAVED hw rank fl wn wt dt rst syb m1).
  Notation X1M fl wn wt dt hw' rank' m1 := (x1m DT WK wksz SPV lo m SAVED fl wn wt dt hw' rank' m1).
  Notation FLB :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; CB 8 f24; CB 8 f32; CB 8 f40; CB 8 f48; CB 8 f56; CB 8 f64; CB 8 f72;
     CB 8 f80; CB 8 f88; C8 (Z_to_bv 64 WK); CB 8 f104; CB 8 f112; CB 8 f120].
  Notation FLS :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); CB 8 f32; CB 8 f40; C8 (Z_to_bv 64 DT); CB 8 f56; CB 8 f64;
     C8 (Z_to_bv 64 (tl + 1)); CB 8 f80; CB 8 f88; C8 (Z_to_bv 64 WK); CB 8 f104; CB 8 f112; CB 8 f120].
  Notation FLF cur sym c104 c112 :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 ux1_K32); C8 (Z_to_bv 64 (DT + 20));
     C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 (- (WK + 1))); C8 (Z_to_bv 64 (tl + 1));
     C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); c104; c112; C8 (Z_to_bv 64 ux1_K120)].
  Hypothesis TL11 : tl < 11.

  Notation RSC := (11 - tl).
  Notation hwk k := (map (resc RSC) (firstn (Z.to_nat k) hw) ++ skipn (Z.to_nat k) hw).
  Notation RSF pc mm hd x1 x5 x6 x7 x11 x12 x13 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r0) x11 x12 x13 (Z_to_bv 64 nbs) x15 x16 x17
         (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 hd) x29 x30 x31).

  Lemma shl2 : forall x, Z.shiftl x 2 = 4 * x.
  Proof. intros x. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.

  Lemma sh32_30 : forall x, 0 <= x < 2^32 -> Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 30 = 4 * x.
  Proof.
    intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
    replace (x * 2^32) with ((4 * x) * 2^30) by lia. rewrite Z.div_mul by lia. reflexivity.
  Qed.

  Ltac rs_chk K := exfalso; rewrite ?sh32_30 in K by lia; lia.

  Lemma rs_not : forall x, 0 <= x < 2^64 -> bv_unsigned (Z_to_bv 64 (Z.lxor x 18446744073709551615)) = 18446744073709551615 - x.
  Proof. intros x Hx. rewrite zb_lxor_ones by lia. apply unsigned_lit. lia. Qed.

  Ltac rs_notv := apply rs_not; lia.

  Lemma resc_val : forall w s, 0 <= w -> 0 <= s < 18446744073709551616 ->
    Z.land ((Z.b2z (w <? 1) + -1) mod 18446744073709551616) s + w = resc s w.
  Proof.
    intros w s Hw Hs. unfold resc. destruct (Z.ltb_spec w 1) as [L|L].
    - assert (w = 0) by lia. subst w. cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l. reflexivity.
    - destruct (Z.eqb_spec w 0); [lia|]. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
      rewrite Z.land_comm, Z.land_ones by lia. change (2^64) with 18446744073709551616. rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma rs_tl : 1 <= tl.
  Proof. destruct STOK as (T & _). lia. Qed.

  Lemma rs_w : forall i, 0 <= i < nbs -> 0 <= Znth i hw <= tl.
  Proof.
    intros i Hi. destruct STOK as (_ & _ & FA & _).
    assert (WSI : Znth i (firstn (Z.to_nat nbs) hw) = Znth i hw).
    { unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
    rewrite <- WSI. apply (Forall_Znth _ _ i FA). rewrite length_firstn. lia.
  Qed.

  Lemma rs_rank : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.
  Proof.
    intros v Hv. destruct STOK as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
  Qed.

  Definition rz_zeroed (k sc : Z) (cur0 cur : list Z) : Prop :=
    Z.of_nat (length cur) = 13 /\ forall v, 0 <= v <= 12 -> Znth v cur = if (k <? v) && (v <=? sc) then 0 else Znth v cur0.

  Lemma rz_zeroed_init : forall sc cur0, Z.of_nat (length cur0) = 13 -> rz_zeroed sc sc cur0 cur0.
  Proof. intros sc cur0 L. split; [exact L|]. intros v Hv. destruct (Z.ltb_spec sc v), (Z.leb_spec v sc); cbn [andb]; try reflexivity; lia. Qed.

  Lemma rz_zeroed_step : forall k sc cur0 cur, rz_zeroed k sc cur0 cur -> 1 <= k <= sc -> sc <= 12 ->
    rz_zeroed (k - 1) sc cur0 (Zupd k 0 cur).
  Proof.
    intros k sc cur0 cur (L & H) Hk Hs. split; [rewrite Zupd_length; exact L|].
    intros v Hv. destruct (Z.eq_dec v k) as [->|NE].
    - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia).
      destruct (Z.ltb_spec (k - 1) k), (Z.leb_spec k sc); cbn [andb]; first [reflexivity | lia].
    - rewrite Znth_Zupd_other by lia. rewrite H by lia.
      destruct (Z.ltb_spec k v), (Z.ltb_spec (k - 1) v), (Z.leb_spec v sc); cbn [andb]; try reflexivity; lia.
  Qed.

  Lemma rz_zeroed_resc : forall sc cur0 cur, shifted sc sc rank cur0 -> rz_zeroed 0 sc cur0 cur -> 0 < sc -> tl + sc = 11 ->
    rank_resc sc rank cur.
  Proof.
    intros sc cur0 cur (L0 & H0) (L & H) Hsc HT. pose proof rs_tl as TL.
    pose proof (st_rank_high _ _ _ STOK) as HI.
    split; [unfold FseNCount.Zlength; exact L|].
    intros v Hv. rewrite H by lia.
    destruct (Z.eqb_spec v 0) as [->|NZ].
    - destruct (Z.ltb_spec 0 0); [lia|]. cbn [andb]. rewrite H0 by lia. destruct (Z.ltb_spec sc 0); [lia | reflexivity].
    - destruct (Z.leb_spec v sc).
      + destruct (Z.ltb_spec 0 v); [|lia]. cbn [andb]. destruct (Z.leb_spec v sc); [reflexivity | lia].
      + destruct (Z.ltb_spec 0 v); cbn [andb]; [| lia]. destruct (Z.leb_spec v sc); [lia|]. rewrite H0 by lia.
        destruct (Z.ltb_spec sc v), (Z.leb_spec v 11); cbn [andb]; try reflexivity; try lia.
        assert (v = 12) by lia. subst v. rewrite (HI 12) by lia. rewrite (HI (12 - sc)) by lia. reflexivity.
  Qed.

  Lemma x1_wloop : forall j m1 k wt dt hd x1 x5 x6 x7 x17 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    Z.to_nat (nbs - k) = j -> X1M FLB (Z_to_bv 64 nbs) wt dt (hwk k) rank m1 -> 0 <= k < nbs ->
    bv_unsigned x17 = 18446744073709551615 - (WK + 1236) ->
    (forall m2 y5 y6 y7, X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) rank m2 ->
       evt usegs POST (RSF 0x1e858 m2 hd x1 y5 y6 y7 (Z_to_bv 64 11) (Z_to_bv 64 RSC) (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 nbs) x17
                         x21 x22 x23 x24 x25 x26 x27 x29 x30 x31)) ->
    evt usegs POST (RSF 0x1e830 m1 hd x1 x5 x6 x7 (Z_to_bv 64 11) (Z_to_bv 64 RSC) (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 k) x17
                      x21 x22 x23 x24 x25 x26 x27 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I KR U17 KONT; [exfalso; lia|].
    destruct I as (DTC & DTLEN & DTBY & HWC & HWKL & HWKB & RK & RKL & S52 & S104 & S980 & S1492 & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof (rs_w k ltac:(lia)) as WKB. pose proof rs_tl as TL1.
    assert (NTHK : Znth k (hwk k) = Znth k hw) by (unfold Znth; apply resc_nth_nat).
    zstep. if_cases KA; zify_cond KA; [exfalso; lia|].
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth usegs m1 (WK + 1236) (hwk k) k a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite NTHK in RD.
    remember (Znth k hw) as w eqn:EW.
    zstep. cbv beta. rewrite (byte_lit w) by lia. clear RD.
    zstep. zstep. zstep. zstep.
    rewrite (resc_val w RSC) by lia.
    assert (RV : 0 <= resc RSC w < 256) by (unfold resc; destruct (w =? 0); lia).
    zstep.
    u8_sok HWC k. zstep. u8_store HWC k (resc RSC w); [reflexivity|].
    assert (STEP : Zupd k (resc RSC w) (hwk k) = hwk (k + 1)).
    { unfold Zupd. rewrite EW. unfold Znth. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. apply resc_step_nat. lia. }
    assert (HWKL' : Z.of_nat (length (hwk (k + 1))) = 256) by (rewrite resc_len_nat; exact HWLEN).
    assert (HWKB' : Forall isbyte (hwk (k + 1))) by (rewrite <- STEP; apply Forall_Zupd; [exact HWKB | lia]).
    rewrite STEP in HWC.
    assert (I' : X1M FLB (Z_to_bv 64 nbs) wt dt (hwk (k + 1)) rank m0).
    { unfold x1m, HUF_TBL_STACK, HUF_DTABLE_BYTES. repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH m0 (k + 1)); [lia | exact I' | lia | exact U17 | exact KONT].
    - assert (EK : k + 1 = nbs) by lia. rewrite EK in I'. rewrite EK. eapply KONT. exact I'.
  Qed.

  Lemma x1_rloop : forall j m1 cur s q wt dt hd x1 x5 x6 x7 x13 x17 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    Z.to_nat (s - RSC) = j -> X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) cur m1 -> shifted s RSC rank cur -> RSC < s <= 11 ->
    q = s - RSC -> bv_unsigned x13 = 18446744073709551615 - WK ->
    (forall m2 cur' y5 y15 y16 y17, X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) cur' m2 -> shifted RSC RSC rank cur' ->
       evt usegs POST (RSF 0x1e8a0 m2 hd x1 y5 x6 x7 (Z_to_bv 64 11) (Z_to_bv 64 RSC) x13 y15 y16 y17
                         x21 x22 x23 x24 x25 x26 x27 x29 x30 x31)) ->
    evt usegs POST (RSF 0x1e864 m1 hd x1 x5 x6 x7 (Z_to_bv 64 11) (Z_to_bv 64 RSC) x13 (Z_to_bv 64 q) (Z_to_bv 64 s) x17
                      x21 x22 x23 x24 x25 x26 x27 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I SH SR EQ U13 KONT; [exfalso; lia|]. subst q.
    destruct I as (DTC & DTLEN & DTBY & HWC & HWKL & HWKB & RK & RKL & S52 & S104 & S980 & S1492 & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof rs_tl as TL1.
    destruct (shifted_step s RSC rank cur SH ltac:(lia) ltac:(lia)) as (ERD & SH').
    zstep. zstep.
    zstep. if_cases KC; zify_cond KC; [rs_chk KC|].
    zstep. rewrite (swrap32_small (s + 0)) by lia.
    zstep. rewrite shl2.
    zstep. if_cases KD; zify_cond KD; [rs_chk KD|].
    zstep. rewrite (Z.mod_small (s - RSC) 4294967296) by lia.
    zstep. rewrite shl2.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m1 WK cur (s - RSC) a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite ERD in RD. pose proof (rs_rank (s - RSC) ltac:(lia)) as RVB.
    zstep. rewrite (sx32w_small (Znth (s - RSC) rank)) by lia. clear RD.
    zstep. zstep. rewrite (swrap32_small (s + -1)) by lia.
    u32st2 RK s (Znth (s - RSC) rank) (Znth (s - RSC) rank).
    change (upd_nat (Z.to_nat s) (Znth (s - RSC) rank) cur) with (Zupd s (Znth (s - RSC) rank) cur) in RK.
    remember (Zupd s (Znth (s - RSC) rank) cur) as cur' eqn:ECUR'.
    assert (RKL' : Z.of_nat (length cur') = 13) by (subst cur'; rewrite Zupd_length; exact RKL).
    clear ECUR'.
    assert (I' : X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) cur' m0).
    { unfold x1m, HUF_TBL_STACK, HUF_DTABLE_BYTES. repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    zstep. zstep. if_cases KE; zify_cond KE.
    - eapply (IH m0 cur' (s + -1) (s - RSC + -1));
        [lia | exact I' | replace (s + -1) with (s - 1) by lia; exact SH' | lia | lia | exact U13 | exact KONT].
    - replace (s - 1) with RSC in SH' by lia. eapply KONT; [exact I' | exact SH'].
  Qed.

  Lemma x1_zloop : forall j m1 k cur0 cur wt dt hd x1 x5 x6 x7 x13 x15 x16 x17 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    Z.to_nat k = j -> X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) cur m1 -> rz_zeroed k RSC cur0 cur -> 1 <= k <= RSC ->
    bv_unsigned x13 = 18446744073709551615 - WK ->
    (forall m2 cur' y12 y15 y16, X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) cur' m2 -> rz_zeroed 0 RSC cur0 cur' ->
       evt usegs POST (RSF 0x1e8c4 m2 hd x1 x5 x6 x7 (Z_to_bv 64 11) y12 x13 y15 y16 x17
                         x21 x22 x23 x24 x25 x26 x27 x29 x30 x31)) ->
    evt usegs POST (RSF 0x1e8a0 m1 hd x1 x5 x6 x7 (Z_to_bv 64 11) (Z_to_bv 64 k) x13 x15 x16 x17
                      x21 x22 x23 x24 x25 x26 x27 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I ZE KR U13 KONT; [exfalso; lia|].
    destruct I as (DTC & DTLEN & DTBY & HWC & HWKL & HWKB & RK & RKL & S52 & S104 & S980 & S1492 & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof rs_tl as TL1.
    zstep. zstep. zstep. if_cases KZ; zify_cond KZ; [rs_chk KZ|].
    zstep. rewrite (Z.mod_small k 4294967296) by lia.
    zstep. rewrite shl2.
    zstep. zstep. rewrite (swrap32_small (k + -1)) by lia.
    u32st2 RK k 0 0.
    change (upd_nat (Z.to_nat k) 0 cur) with (Zupd k 0 cur) in RK.
    pose proof (rz_zeroed_step k RSC cur0 cur ZE ltac:(lia) ltac:(lia)) as ZE'.
    remember (Zupd k 0 cur) as cur' eqn:ECUR'.
    assert (RKL' : Z.of_nat (length cur') = 13) by (subst cur'; rewrite Zupd_length; exact RKL).
    clear ECUR'.
    assert (I' : X1M FLB (Z_to_bv 64 nbs) wt dt (hwk nbs) cur' m0).
    { unfold x1m, HUF_TBL_STACK, HUF_DTABLE_BYTES. repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    zstep. if_cases KF; zify_cond KF.
    - eapply (IH m0 (k + -1) cur0 cur');
        [lia | exact I' | replace (k + -1) with (k - 1) by lia; exact ZE' | lia | exact U13 | exact KONT].
    - replace (k - 1) with 0 in ZE' by lia. eapply KONT; [exact I' | exact ZE'].
  Qed.

  Lemma x1_rescale : forall m1 dt wt hdw x1 x5 x6 x7 x12 x16 x17 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    X1M FLB (Z_to_bv 64 nbs) wt dt hw rank m1 ->
    (forall m2 hw' rank' y1 y5 y6 y7 y11 y12 y13 y16 y17 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31,
       X1M FLB (Z_to_bv 64 nbs) wt dt hw' rank' m2 -> huf_stats_ok (firstn (Z.to_nat nbs) hw') rank' 11 ->
       evt usegs POST (STF 0x1e8c8 m2 y1 y5 y6 y7 (Z_to_bv 64 DT) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r0) y11 y12 y13 (Z_to_bv 64 nbs) (Z_to_bv 64 11) y16 y17
                            (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) y21 y22 y23 y24 y25 y26 y27 (Z_to_bv 64 hdw) y29 y30 y31)) ->
    evt usegs POST (STF 0x1e820 m1 x1 x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r0) (Z_to_bv 64 11) x12 (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x16 x17
                         (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 hdw) x29 x30 x31).
  Proof.
    intros until x31; intros I KONT.
    pose proof rs_tl as TL1. pose proof STOK as (_ & _ & _ & RKL0 & _).
    zstep. rewrite (swrap32_small (11 - tl)) by lia.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep.
    assert (HK0 : hwk 0 = hw) by reflexivity.
    eapply (x1_wloop (Z.to_nat (nbs - 0)) m1 0); [reflexivity | rewrite HK0; exact I | lia | rs_notv |].
    intros m2 y5 y6 y7 I2.
    zstep.
    zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    zstep.
    eapply (x1_rloop (Z.to_nat (11 - RSC)) m2 rank 11); [reflexivity | exact I2 | apply shifted_init; exact RKL0 | lia | lia | rs_notv |].
    intros m3 cur' y5' y15 y16 y17' I3 SH3.
    pose proof I3 as I3'. destruct I3' as (_ & _ & _ & _ & _ & _ & _ & RKL3 & _).
    eapply (x1_zloop (Z.to_nat RSC) m3 RSC cur' cur'); [reflexivity | exact I3 | apply rz_zeroed_init; exact RKL3 | lia | rs_notv |].
    intros m4 cur'' y12 y15' y16' I4 ZE4.
    zstep.
    pose proof (rz_zeroed_resc RSC cur' cur'' SH3 ZE4 ltac:(lia) ltac:(lia)) as RR4.
    assert (EFH : firstn (Z.to_nat nbs) (hwk nbs) = map (resc RSC) (firstn (Z.to_nat nbs) hw)).
    { assert (LL : length (map (resc RSC) (firstn (Z.to_nat nbs) hw)) = Z.to_nat nbs) by (rewrite length_map, length_firstn; lia).
      rewrite firstn_app, LL, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- LL at 1. apply firstn_all. }
    pose proof (huf_stats_rescale _ rank cur'' tl RSC STOK ltac:(lia) ltac:(lia) RR4) as STOK'.
    rewrite <- EFH in STOK'. replace (tl + RSC) with 11 in STOK' by lia.
    eapply KONT; [exact I4 | exact STOK'].
  Qed.
End X1.
