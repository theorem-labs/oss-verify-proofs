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

  Lemma xb_land : forall a b k, 0 <= k -> (Z.land a b / 2^k) mod 256 = Z.land ((a / 2^k) mod 256) ((b / 2^k) mod 256).
  Proof.
    intros a b k Hk. rewrite <- !Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_land.
    change 256 with (2^8). rewrite <- !Z.land_ones by lia.
    rewrite <- (Z.land_diag (Z.ones 8)) at 1. rewrite !Z.land_assoc. f_equal. rewrite <- !Z.land_assoc. f_equal. apply Z.land_comm.
  Qed.

  Lemma xb_lor : forall a b k, 0 <= k -> (Z.lor a b / 2^k) mod 256 = Z.lor ((a / 2^k) mod 256) ((b / 2^k) mod 256).
  Proof.
    intros a b k Hk. rewrite <- !Z.shiftr_div_pow2 by lia. rewrite Z.shiftr_lor.
    change 256 with (2^8). rewrite <- !Z.land_ones by lia. apply Z.land_lor_distr_l.
  Qed.

  Lemma xb_hdr : forall h t K Y, h mod 256 = 12 -> 0 <= t < 256 -> Y = t * 65536 ->
    K mod 256 = 255 -> (K / 256) mod 256 = 0 -> (K / 65536) mod 256 = 0 ->
    Z.lor (Z.land h K) Y mod 256 = 12 /\ (Z.lor (Z.land h K) Y / 256) mod 256 = 0 /\ (Z.lor (Z.land h K) Y / 65536) mod 256 = t.
  Proof.
    intros h t K Y H0 Ht EY K0 K1 K2. subst Y.
    assert (B : forall k, 0 <= k -> (Z.lor (Z.land h K) (t * 65536) / 2^k) mod 256
                  = Z.lor (Z.land ((h / 2^k) mod 256) ((K / 2^k) mod 256)) (((t * 65536) / 2^k) mod 256)).
    { intros k Hk. rewrite xb_lor by lia. rewrite xb_land by lia. reflexivity. }
    split; [| split].
    - pose proof (B 0 ltac:(lia)) as B0. change (2^0) with 1 in B0. rewrite !Z.div_1_r in B0. rewrite B0, H0, K0.
      change (Z.land 12 255) with 12.
      replace ((t * 65536) mod 256) with 0 by (clear - Ht; Z.div_mod_to_equations; lia). reflexivity.
    - pose proof (B 8 ltac:(lia)) as B8. change (2^8) with 256 in B8. rewrite B8, K1, Z.land_0_r.
      replace ((t * 65536 / 256) mod 256) with 0 by (clear - Ht; Z.div_mod_to_equations; lia). reflexivity.
    - pose proof (B 16 ltac:(lia)) as B16. change (2^16) with 65536 in B16. rewrite B16, K2, Z.land_0_r.
      rewrite Z.div_mul by lia. rewrite Z.mod_small by lia. apply Z.lor_0_l.
  Qed.

  Lemma xb_rk : forall k, 0 <= k <= 12 -> 0 <= Znth k rank <= 256.
  Proof.
    intros k Hk. pose proof (st_rank_nonneg _ _ _ STOK k Hk) as RK0.
    pose proof (xsym_step rank k ltac:(lia)) as S1. pose proof (xsym_mono _ _ _ STOK (k + 1) 13 ltac:(lia) ltac:(lia)) as S2.
    pose proof (xsym_nonneg _ _ _ STOK k ltac:(lia)) as S3. rewrite (xsym_total _ _ _ STOK) in S2.
    unfold FseNCount.Zlength in S2. rewrite length_firstn in S2. lia.
  Qed.

  Ltac xb_open I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac xb_close := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES;
                   repeat (split; [first [eassumption | reflexivity | lia] |]); first [eassumption | reflexivity | lia].
  Ltac xb_chk := zstep; let K := fresh "K" in if_cases K; zify_cond K; [exfalso; lia|].
  Ltac xb_ld RK k :=
    let a := cur_mem_addr in
    let RD := fresh "RD" in
    pose proof (u32_znth usegs _ WK rank k a RK ltac:(lia) ltac:(addr_tac)) as RD;
    zstep; rewrite (sx32w_small (Znth k rank)) by (pose proof (xb_rk k ltac:(lia)); lia); clear RD.
  Ltac xb_sum k k1 :=
    let XS := fresh "XS" in
    assert (XS : xsym rank k1 = xsym rank k + Znth k rank) by exact (xsym_step rank k ltac:(lia));
    first [ replace (Z_to_bv 64 (Znth k rank + xsym rank k)) with (Z_to_bv 64 (xsym rank k1)) by (f_equal; lia)
          | replace (Z_to_bv 64 (xsym rank k + Znth k rank)) with (Z_to_bv 64 (xsym rank k1)) by (f_equal; lia) ];
    clear XS.
  Ltac xb_st RST RSTLEN PRE P2 k rst :=
    u32st2 RST k (xsym rank k) (xsym rank k);
    change (upd_nat (Z.to_nat k) (xsym rank k) rst) with (Zupd k (xsym rank k) rst) in RST;
    assert (P2 : forall v, 0 <= v < k + 1 -> Znth v (Zupd k (xsym rank k) rst) = xsym rank v);
    [ intros v Hv; destruct (Z.eq_dec v k) as [->|NE];
      [ apply Znth_Zupd_same; unfold FseNCount.Zlength; lia
      | rewrite Znth_Zupd_other by lia; apply PRE; lia ]
    | ];
    let L2 := fresh "RL" in
    assert (L2 : Z.of_nat (length (Zupd k (xsym rank k) rst)) = 13) by (rewrite Zupd_length; exact RSTLEN);
    clear RSTLEN; rename L2 into RSTLEN.

  Section RS.
    Variables (dt1 : list Z) (syb : list byte) (x1 x5 x6 x7 x8 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word).
    Hypothesis KRS : forall m2 rst y10 y11 y12 y13, X1S FLS (Z_to_bv 64 nbs) (Z_to_bv 64 tl) dt1 rst syb m2 ->
      (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
      evt usegs POST (STF 0x1eb24 m2 x1 x5 x6 x7 x8 (Z_to_bv 64 (WK + 1236)) y10 y11 y12 y13 (Z_to_bv 64 nbs) (Z_to_bv 64 tl)
                          (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 (nbs + -4)) x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK)
                          x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
    Notation RSAT k pc a0 a1 a2 a3 :=
      (forall m2 rst, X1S FLS (Z_to_bv 64 nbs) (Z_to_bv 64 tl) dt1 rst syb m2 -> (forall v, 0 <= v < k -> Znth v rst = xsym rank v) -> k <= tl ->
       evt usegs POST (STF pc m2 x1 x5 x6 x7 x8 (Z_to_bv 64 (WK + 1236)) a0 a1 a2 a3 (Z_to_bv 64 nbs) (Z_to_bv 64 tl)
                           (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 (nbs + -4)) x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK)
                           x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)).

    Ltac xb_br P2 k rst NEXT :=
      zstep; let KB := fresh "KB" in if_cases KB; zify_cond KB;
      [ eapply (KRS _ (Zupd k (xsym rank k) rst)); [xb_close | intros v Hv; apply P2; lia]
      | eapply (NEXT _ _ _ (Zupd k (xsym rank k) rst)); [xb_close | intros v Hv; apply P2; lia | lia] ].
    Ltac xb_mid RK RST RSTLEN PRE k km1 rst NEXT :=
      let P2 := fresh "P2" in
      zstep; zstep; xb_chk; xb_chk; zstep; xb_ld RK k; zstep; xb_sum km1 k; zstep; xb_st RST RSTLEN PRE P2 k rst; zstep;
      xb_br P2 k rst NEXT.

    Lemma xb_rs12 : forall a1 a3, RSAT 12 0x1eafc (Z_to_bv 64 (xsym rank 11)) a1 (Z_to_bv 64 (Znth 11 rank)) a3.
    Proof.
      intros a1 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I.
      let P2 := fresh "P2" in
      zstep; zstep; xb_chk; xb_chk; zstep; xb_sum 11 12; zstep; zstep; xb_st RST RSTLEN PRE P2 12 rst; zstep; xb_chk;
      eapply (KRS _ (Zupd 12 (xsym rank 12) rst)); [xb_close | intros v Hv; apply P2; lia].
    Qed.

    Lemma xb_rs11 : forall a2 a3, RSAT 11 0x1ead0 (Z_to_bv 64 (xsym rank 10)) (Z_to_bv 64 (Znth 10 rank)) a2 a3.
    Proof. intros a2 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 11 10 rst xb_rs12. Qed.

    Lemma xb_rs10 : forall a1 a3, RSAT 10 0x1eaa4 (Z_to_bv 64 (Znth 9 rank)) a1 (Z_to_bv 64 (xsym rank 9)) a3.
    Proof. intros a1 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 10 9 rst xb_rs11. Qed.

    Lemma xb_rs9 : forall a0 a3, RSAT 9 0x1ea78 a0 (Z_to_bv 64 (Znth 8 rank)) (Z_to_bv 64 (xsym rank 8)) a3.
    Proof. intros a0 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 9 8 rst xb_rs10. Qed.

    Lemma xb_rs8 : forall a1 a3, RSAT 8 0x1ea4c (Z_to_bv 64 (Znth 7 rank)) a1 (Z_to_bv 64 (xsym rank 7)) a3.
    Proof. intros a1 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 8 7 rst xb_rs9. Qed.

    Lemma xb_rs7 : forall a0 a3, RSAT 7 0x1ea20 a0 (Z_to_bv 64 (Znth 6 rank)) (Z_to_bv 64 (xsym rank 6)) a3.
    Proof. intros a0 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 7 6 rst xb_rs8. Qed.

    Lemma xb_rs6 : forall a1 a3, RSAT 6 0x1e9f4 (Z_to_bv 64 (Znth 5 rank)) a1 (Z_to_bv 64 (xsym rank 5)) a3.
    Proof. intros a1 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 6 5 rst xb_rs7. Qed.

    Lemma xb_rs5 : forall a0 a3, RSAT 5 0x1e9c8 a0 (Z_to_bv 64 (Znth 4 rank)) (Z_to_bv 64 (xsym rank 4)) a3.
    Proof. intros a0 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 5 4 rst xb_rs6. Qed.

    Lemma xb_rs4 : forall a1 a3, RSAT 4 0x1e99c (Z_to_bv 64 (Znth 3 rank)) a1 (Z_to_bv 64 (xsym rank 3)) a3.
    Proof. intros a1 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 4 3 rst xb_rs5. Qed.

    Lemma xb_rs3 : forall a0 a3, RSAT 3 0x1e970 a0 (Z_to_bv 64 (Znth 2 rank)) (Z_to_bv 64 (xsym rank 2)) a3.
    Proof. intros a0 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 3 2 rst xb_rs4. Qed.

    Lemma xb_rs2 : forall a1 a3, RSAT 2 0x1e944 (Z_to_bv 64 (xsym rank 1)) a1 (Z_to_bv 64 (Znth 1 rank)) a3.
    Proof. intros a1 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I. xb_mid RK RST RSTLEN PRE 2 1 rst xb_rs3. Qed.

    Lemma xb_rs1 : forall a1 a2 a3, RSAT 1 0x1e91c (Z_to_bv 64 (xsym rank 1)) a1 a2 a3.
    Proof.
      intros a1 a2 a3 m2 rst I PRE KT. pose proof STOK as (TLR & _). xb_open I.
      let P2 := fresh "P2" in
      zstep; zstep; xb_chk; xb_chk; zstep; xb_ld RK 1; zstep; xb_st RST RSTLEN PRE P2 1 rst; zstep; xb_br P2 1 rst xb_rs2.
    Qed.
  End RS.

  Lemma x1_build : forall m1 dt wt hdw x1 x5 x6 x7 x11 x12 x13 x16 x17 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    X1M FLB (Z_to_bv 64 nbs) wt dt hw rank m1 -> 0 <= hdw < 2^32 -> hdw mod 256 = 12 ->
    (forall m2 dt2 rst syb y1 y5 y6 y7 y8 y10 y11 y12 y13 y18 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
       X1S FLS (Z_to_bv 64 nbs) (Z_to_bv 64 tl) dt2 rst syb m2 -> x1pref tl 0 dt2 -> (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
       evt usegs POST (STF 0x1eb24 m2 y1 y5 y6 y7 y8 (Z_to_bv 64 (WK + 1236)) y10 y11 y12 y13 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 52))
                            (Z_to_bv 64 (nbs + -4)) y18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (STF 0x1e8c8 m1 x1 x5 x6 x7 (Z_to_bv 64 DT) (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r0) x11 x12 x13 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) x16 x17
                         (Z_to_bv 64 (-44)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 hdw) x29 x30 x31).
  Proof.
    intros until x31; intros I HDWR HDW12 KONT.
    destruct I as (DTC & DTLEN & DTBY & HWC & HWLEN' & HWBY' & RK & RKLEN' & RTS & STS & SYS & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof STOK as (TLR & _).
    destruct (u32arr_of_stk usegs _ (WK + 52) 13%nat ltac:(replace (WK + 52 + 4 * Z.of_nat 13) with (WK + 104) by lia; exact RTS) ltac:(lia)) as (rst0 & RST & RSTLEN0).
    destruct (stk_open usegs _ (WK + 980) (WK + 1236) (WK + 980) 256%nat SYS ltac:(lia) ltac:(lia)) as (syb & SYC & _ & _).
    assert (SYLEN : Z.of_nat (length syb) = 256) by (destruct SYC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; lia).
    apply u8arr_of_rw_cells in SYC. clear RTS SYS.
    assert (L255 : Z.land hdw 255 = 12) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; exact HDW12).
    zstep. zstep. zstep.
    zstep. if_cases KT; zify_cond KT; [rewrite L255 in KT; exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    rewrite (swrap32_small (nbs + -4)) by lia.
    let a := cur_mem_addr in
    pose proof (u8arr_storen_ok usegs _ DT _ 0 4 a DTC ltac:(lia) ltac:(rewrite length_map; lia) ltac:(unfold wa; f_equal; lia)) as SOK.
    zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mx ?a2 (le4 (Z_to_bv 64 ?x))) _) =>
      replace a2 with (wa (DT + 0)) by (unfold wa; f_equal; lia);
      pose proof (u8arr_sw mx DT dt 0 x x DTC ltac:(lia) ltac:(lia) eq_refl) as DTC2
    end.
    clear DTC; store_done; rename DTC2 into DTC.
    lazymatch type of DTC with context [Z.lor (Z.land hdw ?K) ?Y] =>
      assert (EY : Y = tl * 65536)
        by (rewrite Z.shiftr_div_pow2 by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite Z.mod_small by lia;
            replace (tl * 2^56) with (tl * 65536 * 2^40) by lia; apply Z.div_mul; lia);
      destruct (xb_hdr hdw tl K Y HDW12 ltac:(lia) EY eq_refl eq_refl eq_refl) as (B0 & B1 & B2)
    end.
    change (0 + 1) with 1 in DTC. change (0 + 2) with 2 in DTC. change (0 + 3) with 3 in DTC.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?l) => remember l as dt1 eqn:EDT1 end.
    assert (DT1L : length dt1 = length dt) by (subst dt1; rewrite !Zupd_length; reflexivity).
    assert (DT1BY : Forall isbyte dt1) by (subst dt1; repeat (apply Forall_Zupd; [| cbv beta; apply Z.mod_pos_bound; lia]); exact DTBY).
    assert (PREF : x1pref tl 0 dt1).
    { subst dt1. unfold x1pref. split; [| split; [| split]].
      - rewrite (Znth_Zupd_other 3 0), (Znth_Zupd_other 2 0), (Znth_Zupd_other 1 0), Znth_Zupd_same
          by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia). exact B0.
      - rewrite (Znth_Zupd_other 3 1), (Znth_Zupd_other 2 1), Znth_Zupd_same
          by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia). exact B1.
      - rewrite (Znth_Zupd_other 3 2), Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia). exact B2.
      - intros u Hu. lia. }
    clear EDT1.
    zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?signed_lit in KC by lia; lia|].
    pose proof (xb_rk 0 ltac:(lia)) as R0B.
    let a := cur_mem_addr in
    pose proof (u32_znth usegs _ WK rank 0 a RK ltac:(lia) ltac:(addr_tac)) as RD.
    zstep. rewrite (sx32w_small (Znth 0 rank)) by lia. clear RD.
    zstep. rewrite (swrap32_small (tl + 1)) by lia.
    zstep. zstep.
    u32st2 RST 0 0 0.
    change (upd_nat (Z.to_nat 0) 0 rst0) with (Zupd 0 0 rst0) in RST.
    assert (RSTLEN : Z.of_nat (length (Zupd 0 0 rst0)) = 13) by (rewrite Zupd_length; lia).
    zstep. if_cases KZ; zify_cond KZ; [exfalso; lia|].
    assert (X1 : xsym rank 1 = Znth 0 rank).
    { pose proof (xsym_step rank 0 ltac:(lia)) as S1. change (0 + 1) with 1 in S1. rewrite S1. reflexivity. }
    replace (Z_to_bv 64 (Znth 0 rank)) with (Z_to_bv 64 (xsym rank 1)) by (rewrite X1; reflexivity).
    eapply (xb_rs1 dt1 syb).
    - intros m2 rst y10 y11 y12 y13 I3 P3. eapply KONT; [exact I3 | exact PREF | exact P3].
    - xb_close.
    - intros v Hv. replace v with 0 by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). reflexivity.
    - lia.
  Qed.
End X1.
