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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit huf411_kit_x1_defs huf411_kit_x1_fc1 huf411_kit_x1_fc2 huf411_kit_x1_fc4 huf411_kit_x1_fc8 huf411_kit_x1_fcd.
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

  Notation ws := (firstn (Z.to_nat nbs) hw).
  Lemma ws_len : FseNCount.Zlength ws = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.

  Lemma rank_le : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= nbs.
  Proof.
    intros v Hv. destruct STOK as (_ & _ & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v ws) as CB. pose proof ws_len as WL. unfold FseNCount.Zlength in WL. lia.
  Qed.

  Lemma fill_facts : forall w, 1 <= w <= tl ->
    0 <= Znth w rank <= 256 /\ 0 <= xsym rank w /\ xsym rank w + Znth w rank <= 256 /\ 0 <= xcur rank w /\
    0 <= Znth w rank * hw_cells w /\ xcur rank w + Znth w rank * hw_cells w <= 2^tl /\ 2^tl <= 4096 /\ 1 <= hw_cells w <= 2048.
  Proof.
    intros w Hw. pose proof STOK as (TL0 & _).
    pose proof (rank_le w ltac:(lia)) as CNTR.
    pose proof (xcur_nonneg _ _ _ STOK w ltac:(lia)) as CUR0. pose proof (xsym_nonneg _ _ _ STOK w ltac:(lia)) as SYM0.
    assert (P2TL : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (SYMH : xsym rank w + Znth w rank <= 256).
    { rewrite <- (xsym_step rank w ltac:(lia)). pose proof (xsym_mono _ _ _ STOK (w + 1) 13 ltac:(lia) ltac:(lia)) as X.
      rewrite (xsym_total _ _ _ STOK), ws_len in X. lia. }
    assert (LENR : 1 <= hw_cells w <= 2048).
    { split; [unfold hw_cells; destruct (Z.eqb_spec w 0); [lia|]; pose proof (Z.pow_pos_nonneg 2 (w - 1) ltac:(lia) ltac:(lia)); lia | apply hw_cells_bound; lia]. }
    assert (CLB : 0 <= Znth w rank * hw_cells w /\ xcur rank w + Znth w rank * hw_cells w <= 2^tl).
    { rewrite <- (xcur_step rank w ltac:(lia)). pose proof (xcur_mono _ _ _ STOK (w + 1) (tl + 1) ltac:(lia) ltac:(lia)) as X.
      rewrite (xcur_end _ _ _ STOK) in X. split; [nia | lia]. }
    repeat split; lia.
  Qed.

  Lemma c8_read4 : forall mm A cs k v, rw_cells usegs mm A cs -> cell_at cs k = Some (C8 v) ->
    ov_read_bytes usegs mm (wa (A + Z.of_nat k)) 4 = Some (le4 v).
  Proof.
    intros mm A cs k v [[Hwf Hb] _] Hc.
    destruct (cell_at_split _ _ _ (C8 v) Hc) as (pre & post & Ecs & Hsz & _).
    rewrite Ecs in Hwf, Hb. apply cells_wf_app in Hwf. destruct Hwf as [Hwpre _].
    rewrite cells_bytes_app in Hb. cbn [cells_bytes] in Hb.
    apply bytes_at_app in Hb. destruct Hb as [_ Hb].
    rewrite cells_bytes_length in Hb by assumption. rewrite Hsz in Hb.
    apply bytes_at_app in Hb. destruct Hb as [Hb _].
    rewrite <- (Z.add_0_r (A + Z.of_nat k)). change 0%Z with (Z.of_nat 0).
    rewrite (bytes_at_ov_read usegs _ _ _ 0%nat 4%nat Hb) by (cbn [cbytes]; rewrite length_le8; lia).
    reflexivity.
  Qed.

  Lemma rw_cells_C8_CB2 : forall segs mm A pre y z post,
    rw_cells segs mm A (pre ++ C8 y :: C8 z :: post) -> rw_cells segs mm A (pre ++ CB 8 (le8 y) :: CB 8 (le8 z) :: post).
  Proof.
    intros segs mm A pre y z post H. apply rw_cells_C8_CB in H.
    pose proof (rw_cells_C8_CB segs mm A (pre ++ [CB 8 (le8 y)]) z post) as X. rewrite <- !app_assoc in X. exact (X H).
  Qed.

  Lemma flf_cb : forall mm cur sym a b, rw_cells usegs mm (SPV + -240) (FLF cur sym (C8 a) (C8 b)) ->
    rw_cells usegs mm (SPV + -240) (FLF cur sym (CB 8 (le8 a)) (CB 8 (le8 b))).
  Proof.
    intros mm cur sym a b H.
    exact (rw_cells_C8_CB2 usegs mm (SPV + -240) (firstn 13 (FLF cur sym (C8 a) (C8 b))) a b [C8 (Z_to_bv 64 ux1_K120)] H).
  Qed.

  Ltac open_x1s I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                     unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac close_x1s := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [first [eassumption | reflexivity]|]); first [eassumption | reflexivity].

  Lemma not64 : forall x y c, c = 2^64 - 1 -> 0 <= x < 2^64 -> y = - (x + 1) -> Z_to_bv 64 (Z.lxor x c) = Z_to_bv 64 y.
  Proof.
    intros x y c -> Hx ->.
    assert (E : Z.lxor x (2^64 - 1) = 2^64 - 1 - x).
    { pose proof (Z.sub_lxor_2rlandn (2^64-1) x) as H.
      assert (Z.land (Z.lnot (2^64-1)) x = 0).
      { replace (Z.lnot (2^64-1)) with (-(2^64)) by reflexivity.
        apply Z.bits_inj'. intros b Hb. rewrite Z.land_spec, Z.bits_0.
        destruct (Z_lt_dec b 64).
        - replace (-(2^64)) with (Z.shiftl (-1) 64) by reflexivity. rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite (Z.bits_above_log2 x); [apply Bool.andb_false_r| lia |].
          destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia]. }
      rewrite Z.lxor_comm. lia. }
    rewrite E. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    replace (2^64 - 1 - x) with (- (x + 1) + 1 * 2^64) by lia. rewrite Z.mod_add by lia. reflexivity.
  Qed.

  Notation STL pc mm x1 x5 x6 x7 x8 x10 x11 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 x8 (Z_to_bv 64 (-9)) x10 x11 x12 (Z_to_bv 64 (WK + 980)) x14 x15 (Z_to_bv 64 (- (WK + 981))) x17
         (Z_to_bv 64 (-17)) (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (-25)) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Notation KLW w wn wt rst :=
    (forall m2 dt' syb' y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
      X1S (FLF (xcur rank w) (xsym rank w) (C8 (Z_to_bv 64 w)) (C8 (Z_to_bv 64 (Znth w rank)))) wn wt dt' rst syb' m2 ->
      x1pref tl (xcur rank w + Znth w rank * hw_cells w) dt' ->
      evt usegs POST (STL 0x1f29c m2 (Z_to_bv 64 (hw_cells w)) y5 y6 y7 y8 y10 y11 y12 y14 y15 y17 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)).
  Notation KNX w wn wt rst :=
    (forall m3 dt3 syb3 c104 c112 z1 z5 z6 z7 z8 z10 z12 z14 z15 z17 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31,
      w + 1 <= tl ->
      X1S (FLF (xcur rank (w + 1)) (xsym rank (w + 1)) (CB 8 c104) (CB 8 c112)) wn wt dt3 rst syb3 m3 ->
      x1pref tl (xcur rank (w + 1)) dt3 ->
      evt usegs POST (STL 0x1ed2c m3 z1 z5 z6 z7 z8 z10 (Z_to_bv 64 (w + 1)) z12 z14 z15 z17 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31)).

  Lemma x1_done : forall m2 dt2 rst syb2 wn wt cur sym c104 c112 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    X1S (FLF cur sym (C8 c104) (C8 c112)) wn wt dt2 rst syb2 m2 -> x1pref tl (2^tl) dt2 ->
    evt usegs POST (STF 0x1f2ec m2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I (H0 & H1 & H2 & HP). open_x1s I. pose proof STOK as (TLR & _).
    zstep.
    assert (P2TL : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (NTH : forall k, 0 <= k < Z.of_nat (length dt2) -> nth_error (map (Z_to_bv 8) dt2) (Z.to_nat k) = Some (Z_to_bv 8 (Znth k dt2))).
    { intros k Hk. apply nth_error_map_Znth. lia. }
    assert (HL : Z.of_nat (length (map (Z_to_bv 8) dt2)) = HUF_DTABLE_BYTES) by (rewrite length_map; exact DTLEN).
    assert (WKS : stk usegs m2 WK (WK + wksz)).
    { apply u8arr_of_u32arr in RK, RST. apply rw_cells_of_u8arr in RK, RST, SYC, HWC. apply stk_of_rw_cells in RK, RST, SYC, HWC.
      cbn [cells_size csize] in RK, RST, SYC, HWC. rewrite u32s_length, length_map in RK, RST. rewrite length_map in HWC.
      apply (stk_merge usegs m2 WK (WK + 52) (WK + wksz)); [replace (WK + 52) with (WK + Z.of_nat (4 * length rank + 0)) by lia; exact RK| |lia].
      apply (stk_merge usegs m2 (WK + 52) (WK + 104) (WK + wksz)); [replace (WK + 104) with (WK + 52 + Z.of_nat (4 * length rst + 0)) by lia; exact RST| |lia].
      apply (stk_merge usegs m2 (WK + 104) (WK + 980) (WK + wksz)); [exact STS| |lia].
      apply (stk_merge usegs m2 (WK + 980) (WK + 1236) (WK + wksz)); [replace (WK + 1236) with (WK + 980 + Z.of_nat (length syb2 + 0)) by lia; exact SYC| |lia].
      apply (stk_merge usegs m2 (WK + 1236) (WK + 1492) (WK + wksz)); [replace (WK + 1492) with (WK + 1236 + Z.of_nat (length hw + 0)) by lia; exact HWC| exact WKR |lia]. }
    assert (FS : stk usegs m2 (SPV + -240) (SPV + -104)).
    { apply stk_of_rw_cells in F0, NSC. rewrite F0SZ in F0. cbn [cells_size csize Nat.add] in NSC.
      apply (stk_merge usegs m2 (SPV + -240) (SPV + -112) (SPV + -104));
        [replace (SPV + -112) with (SPV + -240 + Z.of_nat 128) by lia; exact F0 | replace (SPV + -104) with (SPV + -112 + Z.of_nat 8) by lia; exact NSC | lia]. }
    eapply x1_exit_stk with (dtb' := map (Z_to_bv 8) dt2) (r := r0); try eassumption.
    - split; [exact HL|]. rewrite <- H0. exact (NTH 0 ltac:(lia)).
    - lia.
    - intros _. split.
      + split; [split; [exact HL | rewrite <- H0; exact (NTH 0 ltac:(lia))]|].
        exists (Z_to_bv 8 0), tl. split; [rewrite <- H1; exact (NTH 1 ltac:(lia))|]. split; [rewrite <- H2; exact (NTH 2 ltac:(lia))|].
        split; [lia|]. split; [intros NZ; exfalso; apply NZ; reflexivity|].
        change (negb (bv_unsigned (Z_to_bv 8 0) =? 0)) with false. intros i Hi.
        exists (Z_to_bv 8 (Znth (4 + 2 * i) dt2)). split; [replace (2 * i + 4) with (4 + 2 * i) by lia; apply (NTH (4 + 2 * i)); lia|].
        specialize (HP i Hi). rewrite byte_lit by lia. lia.
      + exists (Z_to_bv 8 0). split; [rewrite <- H1; exact (NTH 1 ltac:(lia))|]. split; [intros NZ; exfalso; apply NZ; reflexivity | intros E; discriminate E].
  Qed.

  Lemma x1_latch : forall w wn wt rst, 1 <= w <= tl -> KNX w wn wt rst -> KLW w wn wt rst.
  Proof.
    intros w wn wt rst WR NEXT. intros until y31; intros I PR.
    destruct (fill_facts w WR) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    pose proof STOK as (TLR & _).
    assert (XS : xsym rank w + Znth w rank = xsym rank (w + 1)) by (rewrite (xsym_step rank w) by lia; lia).
    assert (XC : xcur rank w + Znth w rank * hw_cells w = xcur rank (w + 1)) by (rewrite (xcur_step rank w) by lia; lia).
    remember (Znth w rank) as count eqn:ECNT. remember (hw_cells w) as len eqn:ELEN.
    remember (xcur rank w) as cur eqn:ECUR. remember (xsym rank w) as sym eqn:ESYM.
    open_x1s I.
    pose proof (c8_read4 _ _ _ 88%nat (Z_to_bv 64 sym) F0 eq_refl) as HR.
    zstep. rewrite (sx32w_small sym) by lia.
    zstep. zstep. zstep. rewrite (swrap32_small (sym + count)) by lia.
    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    zstep. zstep. zstep. rewrite (swrap32_small (count * len)) by lia.
    zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. rewrite (swrap32_small (count * len + 0)) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => match goal with H : rw_cells usegs mm (SPV + -240) _ |- _ =>
      pose proof (c8_read4 _ _ _ 80%nat (Z_to_bv 64 cur) H eq_refl) as HR2 end end.
    zstep. rewrite (sx32w_small cur) by lia.
    zstep. zstep. rewrite (swrap32_small (cur + count * len)) by lia.
    zstep. zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    zstep. zstep. zstep. zstep. if_cases K4; zify_cond K4.
    - match goal with H : rw_cells usegs _ (SPV + -240) (FLF (cur + count * len) (sym + count) _ _) |- _ =>
        apply flf_cb in H; rewrite XS, XC in H end.
      eapply NEXT; [lia | close_x1s | rewrite <- XC; exact PR].
    - eapply x1_done; [close_x1s |].
      replace (2^tl) with (cur + count * len); [exact PR|].
      rewrite <- (xcur_end _ _ _ STOK). replace (tl + 1) with (w + 1) by lia. lia.
  Qed.

  Lemma x1_body : forall w wn wt rst m1 dt syb c104 c112 x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    1 <= w <= tl -> KLW w wn wt rst ->
    X1S (FLF (xcur rank w) (xsym rank w) (CB 8 c104) (CB 8 c112)) wn wt dt rst syb m1 -> x1pref tl (xcur rank w) dt ->
    evt usegs POST (STL 0x1ed2c m1 x1 x5 x6 x7 x8 x10 (Z_to_bv 64 w) x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros WR KL I PR.
    destruct (fill_facts w WR) as (CNTR & SYM0 & SYMH & CUR0 & CL0 & CLH & P2TL & LENR).
    pose proof STOK as (TLR & _).
    assert (SLOTS : forall s, 0 <= s < Znth w rank ->
              0 <= xsym rank w + s < 256 /\ 0 <= xcur rank w + s * hw_cells w /\ xcur rank w + s * hw_cells w + hw_cells w <= 4096).
    { intros s Hs. destruct (fill_slot _ _ _ STOK w s WR Hs) as (A & B & C). rewrite ws_len in A. lia. }
    assert (P2W : 2 <= 2^w <= 4096) by (split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (LENW : (w = 1 /\ hw_cells w = 1) \/ (w = 2 /\ hw_cells w = 2) \/ (w = 3 /\ hw_cells w = 4) \/ (w = 4 /\ hw_cells w = 8) \/
                   (5 <= w /\ hw_cells w = 16 * 2^(w - 5))).
    { unfold hw_cells. destruct (Z.eqb_spec w 0); [lia|].
      destruct (Z.eq_dec w 1) as [->|N1]; [left; split; reflexivity|]. destruct (Z.eq_dec w 2) as [->|N2]; [right; left; split; reflexivity|].
      destruct (Z.eq_dec w 3) as [->|N3]; [right; right; left; split; reflexivity|]. destruct (Z.eq_dec w 4) as [->|N4]; [right; right; right; left; split; reflexivity|].
      right; right; right; right. split; [lia|]. change 16 with (2^4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    remember (Znth w rank) as count eqn:ECNT. remember (hw_cells w) as len eqn:ELEN.
    remember (xcur rank w) as cur eqn:ECUR. remember (xsym rank w) as sym eqn:ESYM.
    assert (CURH : cur <= 4096) by lia.
    open_x1s I.
    zstep. zstep. zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    zstep. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs _ WK rank w a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite <- ECNT in RD.
    zstep. rewrite (sx32w_small count) by lia. clear RD.
    zstep. zstep. zstep. zstep. rewrite (sllw_pow2 w) by lia.
    zstep.
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) => lazymatch R with TNode (TNode _ (Some (Z_to_bv 64 ?e)) _) _ _ =>
      replace e with len by (rewrite ELEN; clear - WR TLR;
        assert (WC : w = 1 \/ w = 2 \/ w = 3 \/ w = 4 \/ w = 5 \/ w = 6 \/ w = 7 \/ w = 8 \/ w = 9 \/ w = 10 \/ w = 11 \/ w = 12) by lia;
        destruct WC as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; vm_compute; reflexivity) end end.
    zstep. zstep. rewrite (swrap32_small (tl + 1 - w)) by lia.
    zstep. zstep.
    destruct LENW as [(W1 & L1) | [(W2 & L2) | [(W3 & L4) | [(W4 & L8) | (W5 & L16)]]]].
    - if_cases K2; zify_lts K2; try (exfalso; lia).
      zstep. if_cases K3; zify_cond K3; try (exfalso; lia).
      eapply x1_fill1 with (hw := hw) (rank := rank) (rst := rst) (wn := wn) (wt := wt) (w := w) (cur := cur) (sym := sym) (count := count) (len := len)
        (nb := tl + 1 - w) (dt := dt) (syb := syb).
      all: first [exact KL | eassumption | lia | close_x1s].
    - if_cases K2; zify_lts K2; try (exfalso; lia).
      zstep. if_cases K3; zify_cond K3; try (exfalso; lia).
      zstep. zstep. if_cases K4; zify_cond K4; try (exfalso; lia).
      eapply x1_fill2 with (hw := hw) (rank := rank) (rst := rst) (wn := wn) (wt := wt) (w := w) (cur := cur) (sym := sym) (count := count) (len := len)
        (nb := tl + 1 - w) (dt := dt) (syb := syb).
      all: first [exact KL | eassumption | lia | close_x1s].
    - if_cases K2; zify_lts K2; try (exfalso; lia).
      zstep. zstep. if_cases K3; zify_cond K3; try (exfalso; lia).
      eapply x1_fill4 with (hw := hw) (rank := rank) (rst := rst) (wn := wn) (wt := wt) (w := w) (cur := cur) (sym := sym) (count := count) (len := len)
        (nb := tl + 1 - w) (dt := dt) (syb := syb).
      all: first [exact KL | eassumption | lia | close_x1s].
    - if_cases K2; zify_lts K2; try (exfalso; lia).
      zstep. zstep. if_cases K3; zify_cond K3; try (exfalso; lia).
      zstep. zstep. if_cases K4; zify_cond K4; try (exfalso; lia).
      eapply x1_fill8 with (hw := hw) (rank := rank) (rst := rst) (wn := wn) (wt := wt) (w := w) (cur := cur) (sym := sym) (count := count) (len := len)
        (nb := tl + 1 - w) (dt := dt) (syb := syb).
      all: first [exact KL | eassumption | lia | close_x1s].
    - assert (Q1 : 1 <= 2^(w - 5)) by (pose proof (Z.pow_pos_nonneg 2 (w - 5) ltac:(lia) ltac:(lia)); lia).
      assert (QH : 2^(w - 5) <= 128) by (change 128 with (2^7); apply Z.pow_le_mono_r; lia).
      remember (2^(w - 5)) as Q eqn:EQ. clear EQ.
      if_cases K2; zify_lts K2; try (exfalso; lia).
      zstep. zstep. if_cases K3; zify_cond K3; try (exfalso; lia).
      zstep. zstep. if_cases K4; zify_cond K4; try (exfalso; lia).
      eapply x1_fillD with (hw := hw) (rank := rank) (rst := rst) (wn := wn) (wt := wt) (w := w) (cur := cur) (sym := sym) (count := count) (len := len)
        (nb := tl + 1 - w) (Q := Q) (dt := dt) (syb := syb).
      all: first [exact KL | eassumption | lia | close_x1s].
  Qed.

  Lemma x1_fill_loop : forall j w wn wt rst m1 dt syb c104 c112 x1 x5 x6 x7 x8 x10 x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    Z.to_nat (tl + 1 - w) = j -> 1 <= w <= tl ->
    X1S (FLF (xcur rank w) (xsym rank w) (CB 8 c104) (CB 8 c112)) wn wt dt rst syb m1 -> x1pref tl (xcur rank w) dt ->
    evt usegs POST (STL 0x1ed2c m1 x1 x5 x6 x7 x8 x10 (Z_to_bv 64 w) x12 x14 x15 x17 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ WR I PR; [exfalso; lia|].
    eapply x1_body; [exact WR | | exact I | exact PR].
    apply x1_latch; [exact WR|].
    intros until z31; intros WN I3 PR3.
    eapply IH; [lia | lia | exact I3 | exact PR3].
  Qed.

  Lemma x1_fill : forall m1 dt rst syb wn wt x1 x5 x6 x7 x8 x9 x10 x11 x12 x14 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    X1S FLS wn wt dt rst syb m1 -> x1pref tl 0 dt ->
    evt usegs POST (STF 0x1ecc0 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (WK + 980)) x14 (Z_to_bv 64 tl) x16 x17 x18 (Z_to_bv 64 (DT + 4)) x20
                         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I PR0. open_x1s I. pose proof STOK as (TLR & _).
    zstep. if_cases KA; zify_cond KA; [exfalso; lia|].
    zstep. zstep. zstep. rewrite (not64 WK (- (WK + 1))) by first [reflexivity | lia].
    zstep. zstep. rewrite (not64 (WK + 980) (- (WK + 981))) by first [reflexivity | lia].
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs _ WK rank 0 a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. pose proof (rank_le 0 ltac:(lia)) as R0B. rewrite (sx32w_small (Znth 0 rank)) by lia. clear RD.
    do 5 zstep. do 3 zstep.
    zstep. rewrite (Z.mod_small (tl + 1)) by lia.
    do 3 zstep. do 3 zstep. do 2 zstep.
    assert (XC1 : xcur rank 1 = 0) by (unfold xcur; change (Z.to_nat 1) with 1%nat; cbn [psum]; change (Z.of_nat 0) with 0; change (hw_cells 0) with 0; lia).
    assert (XS1 : xsym rank 1 = Znth 0 rank) by (unfold xsym; change (Z.to_nat 1) with 1%nat; cbn [psum]; change (Z.of_nat 0) with 0; lia).
    match goal with H : rw_cells usegs _ (SPV + -240) (_ :: _ :: _ :: _ :: C8 ?k4 :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: C8 ?k15 :: nil) |- _ =>
      replace k4 with (Z_to_bv 64 ux1_K32) in H by (apply bv_eq; reflexivity);
      replace k15 with (Z_to_bv 64 ux1_K120) in H by (apply bv_eq; reflexivity);
      rewrite <- XS1 in H;
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (xcur rank 1)) in H by (rewrite XC1; reflexivity)
    end.
    eapply (x1_fill_loop (Z.to_nat (tl + 1 - 1)) 1); [reflexivity | lia | close_x1s | rewrite XC1; exact PR0].
  Qed.
End X1.
