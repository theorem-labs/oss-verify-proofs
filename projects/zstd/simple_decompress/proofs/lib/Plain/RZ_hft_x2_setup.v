(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_pre RZ_hft_x2_wl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X2S.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV SRC n DT WK wksz lo : Z) (src dtb : list byte).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.
  Hypothesis SRCLEN : Z.of_nat (length src) = n.  Hypothesis SRCL : 4096 <= SRC.  Hypothesis NR : n < 2^32.  Hypothesis SRCH : SRC + n < 2^47.
  Hypothesis HDR : huf_hdr_ok dtb.  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis OFFSRC : SRC + n <= lo \/ SPV <= SRC.  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis DTSRC : DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT.  Hypothesis WKSRC : WK + wksz <= SRC \/ SRC + n <= WK.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo true m).
  Notation MUNCH := [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -272)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma x2_exit_err : forall m1 dtb' r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr psegs m1 DT dtb' -> huf_hdr_ok dtb' -> stk psegs m1 WK (WK + wksz) -> stk psegs m1 lo (SPV + -272) ->
    stk psegs m1 (SPV + -272) (SPV + -104) -> rw_cells psegs m1 (SPV + -104) SAVED ->
    mem_inv psegs m1 -> munch MUNCH m m1 -> wmono psegs m m1 -> 0 <= r < 2^64 -> zd_is_error r = true ->
    evt psegs POST (STF 0x1d9c4 m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC HDR' WKS STK STF0 FSAV MI MU WM RR RE. unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    zstep. do 13 zstep. zstep.
    apply stk_of_rw_cells in FSAV. cbn [cells_size csize Nat.add] in FSAV.
    assert (STK' : stk psegs m1 lo SPV).
    { apply (stk_merge psegs m1 lo (SPV + -272) SPV STK); [|lia].
      apply (stk_merge psegs m1 (SPV + -272) (SPV + -104) SPV STF0); [|lia].
      replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by lia. exact FSAV. }
    zstep. apply evt_done. unfold huf_rd_post.
    do 14 eexists. exists m1, r, dtb'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact WKS|]. split; [exact DTC|]. split; [exact HDR'|]. split; [exact RR|]. intros E. rewrite RE in E. discriminate E.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_maxw_loop : forall j mm (ws rank : list Z) tl T v x1 x5 x6 x7 x8 x9 x10 x11 x12 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    Z.to_nat v = j -> huf_stats_ok ws rank tl -> tl <= T <= 12 -> mem_inv psegs mm ->
    u32arr psegs mm (WK + 624) (map (Z_to_bv 64) rank) -> 0 <= v <= tl -> (forall u, v < u <= tl -> Znth u rank = 0) ->
    (forall maxW y16, 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
       evt psegs POST (STF 0x1d0a4 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (tl - maxW + 1)) (Z_to_bv 64 (maxW - 1)) (Z_to_bv 64 (WK + 676)) y16 x17
                           (Z_to_bv 64 (WK + 624)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (STF 0x1d088 mm x1 x5 x6 x7 x8 x9 x10 x11 x12 (Z_to_bv 64 (tl - v)) (Z_to_bv 64 v) (Z_to_bv 64 (WK + 676)) x16 x17
                        (Z_to_bv 64 (WK + 624)) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ SOK TT MI RK VR ZR KONT.
    { exfalso. assert (v = 0) by lia. subst v. apply (some_weight ws rank tl T SOK TT). intros u Hu. apply ZR. lia. }
    assert (TLR : 1 <= tl <= 12) by (destruct SOK as (H & _); exact H).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    zstep. zstep. rewrite (zext32_sh30 v) by lia.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs mm (WK + 624) rank v a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep.
    pose proof (st_rank_nonneg ws rank tl SOK v ltac:(lia)) as C0.
    assert (CH : Znth v rank <= 256).
    { destruct SOK as (_ & (_ & LEN) & _ & _ & CNT & _). rewrite (CNT v ltac:(lia)). unfold hcount.
      pose proof (count_occ_bound Z.eq_dec v ws). unfold FseNCount.Zlength in LEN. lia. }
    rewrite (sx32w_small (Znth v rank)) by lia. clear RD.
    zstep. zstep. rewrite (swrap32_small (tl - v + 1)) by lia.
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (tl - v + 1)) with (Z_to_bv 64 (tl - (v + -1))) by (f_equal; lia).
      eapply (IH mm ws rank tl T (v + -1)); try eassumption; try lia.
      intros u Hu. destruct (Z.eq_dec u v) as [->|NE]; [exact KB | apply ZR; lia].
    - replace (Z_to_bv 64 (v + -1)) with (Z_to_bv 64 (v - 1)) by (f_equal; lia).
      eapply (KONT v); [lia |].
      intros u Hu. destruct (Z_le_gt_dec u tl) as [LE|GT]; [apply ZR; lia | apply (st_rank_high ws rank tl SOK u); lia].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_setup : forall m1 (dt hw rank rs00 : list Z) (tl T maxW nbs r0 hdw : Z) flags fj4 fj6 fj7 fj8 fj9 fj10 fj11 fj12 fj14 fj15 fj16 fj17 fj18
      x1 x5 x6 x7 x10 x12 x14 x16 x17 x19 x20 x21 x22 x26 x27 x29 x30 x31,
    mem_inv psegs m1 -> munch MUNCH m m1 -> wmono psegs m m1 ->
    u8arr psegs m1 DT (map (Z_to_bv 8) dt) -> Z.of_nat (length dt) = 16388 -> Forall (fun c => 0 <= c < 256) dt -> Znth 0 dt = 12 ->
    0 <= hdw < 4294967296 -> hdw mod 256 = 12 ->
    stk psegs m1 WK (WK + 624) -> u32arr psegs m1 (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr psegs m1 (WK + 676) (map (Z_to_bv 64) rs00) -> Z.of_nat (length rs00) = 15 ->
    stk psegs m1 (WK + 736) (WK + 992) ->
    u8arr psegs m1 (WK + 992) (map (Z_to_bv 8) hw) -> Z.of_nat (length hw) = 256 -> Forall (fun c => 0 <= c < 256) hw ->
    stk psegs m1 (WK + 1248) (WK + 1248 + 876) -> stk psegs m1 (WK + 2124) (WK + wksz) -> 2124 <= wksz ->
    rw_cells psegs m1 (SPV + -272)
      [C8 (Z_to_bv 64 876); C8 flags; C8 (Z_to_bv 64 (hdw ≫ 24)); C8 (Z_to_bv 64 r0); CB 8 fj4; C8 (Z_to_bv 64 DT); CB 8 fj6; CB 8 fj7; CB 8 fj8; CB 8 fj9;
       CB 8 fj10; CB 8 fj11; CB 8 fj12; C8 (Z_to_bv 64 (tl + 1)); CB 8 fj14; CB 8 fj15; CB 8 fj16; CB 8 fj17; CB 8 fj18; C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells psegs m1 (SPV + -112) [C4 (Z_to_bv 64 nbs); C4 (Z_to_bv 64 tl)] ->
    rw_cells psegs m1 (SPV + -104) SAVED -> stk psegs m1 lo (SPV + -272) ->
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 -> 1 <= r0 <= n ->
    tl <= T <= 12 -> 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
    evt psegs POST (STF 0x1d0ac m1 x1 x5 x6 x7 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (WK + 992)) x10 (Z_to_bv 64 (WK + 680)) x12 (Z_to_bv 64 (tl - maxW + 1)) x14
                        (Z_to_bv 64 (WK + 676)) x16 x17 (Z_to_bv 64 (WK + 624)) x19 x20 x21 x22 (Z_to_bv 64 T) (Z_to_bv 64 hdw) (Z_to_bv 64 WK) x26 x27
                        (Z_to_bv 64 tl) x29 x30 x31).
  Proof.
    intros until x31; intros MI MU WM DTC DTL' DTBY DTZ0 HDWR HDW12 RVS RK RS0A RS00L SYS HWC HWLEN HWBY CWK' WKR WK2124 F0 NSC FSAV STK' SOK NBR R0N TT MAXW HIGH.
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof SOK as (TLR & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    zstep. rewrite (swrap32_small (tl - (tl - maxW + 1))) by lia.
    zstep. rewrite (swrap32_small (tl - (tl - maxW + 1) + 2)) by lia. replace (tl - (tl - maxW + 1) + 2) with (maxW + 1) by lia.
    zstep. zstep. zstep. if_cases K5; zify_cond K5; [exfalso; lia|].
    zstep. zstep. zstep. zstep. rewrite (zext32_sh30 (maxW + 1)) by lia.
    zstep. zstep.
    replace (Z_to_bv 64 (WK + 628)) with (Z_to_bv 64 (WK + 624 + 4 * 1)) by (f_equal; lia).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (xs1 rank 1)) by (rewrite (xs1_1 rank); reflexivity).
    eapply evt_cut.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply x2_p2_loop with (WK := WK) (m0 := mm) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rs0 := rs00) (rs := rs00) (w := 1)
                               (j := Z.to_nat (maxW + 1 - 1)); try eassumption; try lia; try reflexivity end.
      - apply munch_refl.
      - apply wmono_refl. }
    unfold x2_p2_post. post_call psegs m0.
    rename POST into RS2M. rename PC into RSA. rename PC0 into RSL.
    pose proof (xs1_nonneg (firstn (Z.to_nat nbs) hw) rank tl SOK (maxW + 1) ltac:(lia)) as XT0.
    pose proof (xs1_total (firstn (Z.to_nat nbs) hw) rank tl SOK maxW ltac:(lia) HIGH) as XTT.
    pose proof (st_rank_nonneg (firstn (Z.to_nat nbs) hw) rank tl SOK 0 ltac:(lia)) as CNTZ.
    assert (WSL : FseNCount.Zlength (firstn (Z.to_nat nbs) hw) = nbs) by (unfold FseNCount.Zlength; rewrite length_firstn; lia).
    zstep. zstep.
    u32w RSA 1 (xs1 rank (maxW + 1)) (xs1 rank (maxW + 1)).
    zstep. zstep. rewrite (zx32w_small nbs) by lia.
    zstep. zstep.
    assert (SH30 : ((maxW + 1) ≪ 32 mod 18446744073709551616) ≫ 30 = 4 * (maxW + 1)).
    { rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2^32) with 4294967296. change (2^30) with 1073741824. Z.div_mod_to_equations. lia. }
    rewrite SH30.
    u32w RSA (maxW + 2) (xs1 rank (maxW + 1)) (xs1 rank (maxW + 1)).
    zstep. zstep. if_cases K6; zify_cond K6; [exfalso; lia|].
    zstep.
    destruct (stk_open psegs _ (WK + 736) (WK + 992) (WK + 736) 256%nat SYS ltac:(lia) ltac:(lia)) as (sy0 & SYC & _ & _).
    pose proof (rw_cells_CB_length _ _ _ _ _ SYC) as SY0L.
    apply u8arr_of_rw_cells in SYC. clear SYS.
    eapply evt_cut.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply x2_p3_loop with (WK := WK) (m0 := mm) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (hw := hw) (nbs := nbs) (i := 0)
                               (j := Z.to_nat (nbs - 0)); try eassumption; try lia; try reflexivity end.
      - apply munch_refl.
      - apply wmono_refl.
      - rewrite !Zupd_length. exact RSL.
      - intros w Hw. change (firstn (Z.to_nat 0) (firstn (Z.to_nat nbs) hw)) with (@nil Z). unfold hcount at 1. cbn [count_occ Z.of_nat]. unfold psort.
        destruct (Z.eqb_spec w 0) as [->|NE].
        + rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). lia.
        + rewrite !Znth_Zupd_other by lia. rewrite (RS2M w ltac:(lia)). lia. }
    unfold x2_p3_post. post_call psegs m0.
    rename POST into RS3M. rename PC into RSA. rename PC0 into RSL3. rename PC1 into SYC. rename PC2 into SYL.
    zstep.
    u32w RSA 1 0 0.
    zstep. if_cases K7; zify_cond K7; [exfalso; lia|].
    zstep. zstep. zstep.
    zstep. rewrite (swrap32_small (tl + 1 - (tl - maxW + 1))) by lia. replace (tl + 1 - (tl - maxW + 1)) with maxW by lia.
    zstep. zstep. zstep.
    zstep. rewrite (swrap32_small (T - tl)) by lia.
    zstep. zstep. zstep.
    rewrite (Z.mod_small (maxW + 1) 4294967296) by lia.
    replace ((maxW + 1) ≪ 2) with (4 * (maxW + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    destruct (u32arr_of_stk psegs _ WK 156%nat ltac:(replace (WK + 4 * Z.of_nat 156) with (WK + 624) by lia; exact RVS) ltac:(lia)) as (rvl0 & RVA & RVL0).
    clear RVS.
    replace (Z_to_bv 64 (WK + 628)) with (Z_to_bv 64 (WK + 624 + 4 * 1)) by (f_equal; lia).
    replace (Z_to_bv 64 (T - tl)) with (Z_to_bv 64 (T - tl + (1 - 1))) by (f_equal; lia).
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (rv0 rank tl T 1)) by (rewrite (rv0_1 rank tl T); reflexivity).
    eapply evt_cut.
    { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        eapply x2_p4_loop with (WK := WK) (m0 := mm) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rvl := rvl0) (w := 1)
                               (j := Z.to_nat (maxW + 1 - 1)); try eassumption; try lia; try reflexivity end.
      - apply munch_refl.
      - apply wmono_refl. }
    unfold x2_p4_post.
    lazymatch goal with MIx : mem_inv psegs ?mm |- _ => post_call psegs mm end.
    rename POST into RV4M. rename PC into RVA. rename PC0 into RVL4.
    replace (Z_to_bv 64 (tl - maxW + 1)) with (Z_to_bv 64 (tl + 1 - maxW)) by (f_equal; lia).
    eapply evt_cut.
    { zstep. rewrite (swrap32_small (T - (tl + 1 - maxW))) by lia.
      zstep. rewrite (swrap32_small (T - (tl + 1 - maxW) + 1)) by lia.
      zstep. if_cases KR; zify_cond KR.
      2:{ zstep. zstep. zstep. zstep. zstep. zstep.
          replace (((tl + 1 - maxW) ≪ 32 mod 18446744073709551616 * 223338299392) ≫ 64) with (52 * (tl + 1 - maxW))
            by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296; change (2^64) with 18446744073709551616;
                rewrite (Z.mod_small ((tl + 1 - maxW) * 4294967296)) by lia; Z.div_mod_to_equations; lia).
          rewrite (Z.mod_small (tl + 1 - maxW) 4294967296) by lia.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
            eapply x2_p5_loop with (WK := WK) (m0 := mm) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rvl := x25) (c := tl + 1 - maxW)
                                   (j := Z.to_nat (T - (tl + 1 - maxW) + 1 - (tl + 1 - maxW))); try eassumption; try lia; try reflexivity end.
          - apply munch_refl.
          - apply wmono_refl.
          - unfold rows_inv. split; [exact RVL4|]. split; [exact RV4M|]. split; intros; lia. }
      apply evt_done. unfold x2_p5_post. do 6 eexists. do 2 eexists. split; [reflexivity|].
      split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [eassumption|]. split; [exact RVA|].
      unfold rows_inv. split; [exact RVL4|]. split; [exact RV4M|]. split; intros; lia. }
    unfold x2_p5_post.
    lazymatch goal with MIx : mem_inv psegs ?mm |- _ => post_call psegs mm end.
    rename POST into ROWS. rename PC into RVA. pose proof (proj1 ROWS) as RVL5.
    zstep. zstep. if_cases K8; [exfalso; zify_cond K8; lia|]. clear K8.
    zstep. zstep. rewrite (swrap32_small (tl + 1 - T)) by lia.
    zstep. zstep. zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (tl - maxW + 1)) with (Z_to_bv 64 (tl + 1 - maxW)) in F0 by (f_equal; lia).
    lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13] j post F0) as [v112 F1] end. cbn [app] in F1. clear F0.
    lazymatch type of F1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14] j post F1) as [v120 F0] end. cbn [app] in F0. clear F1.
    lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15] j post F0) as [v128 F1] end. cbn [app] in F1. clear F0.
    lazymatch type of F1 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16] j post F1) as [v136 F0] end. cbn [app] in F0. clear F1.
    lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: CB 8 ?j :: ?post) =>
      destruct (cb8_as_c8 psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17] j post F0) as [v144 F1] end. cbn [app] in F1. clear F0.
    assert (FR : rw_cells psegs m0 (SPV + -272)
                   (x2_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK (Z_to_bv 64 876) flags (Z_to_bv 64 (hdw ≫ 24)) r0 (Z_to_bv 64 hdw)
                             (tl + 1 - T) maxW (tl + 1 - maxW) (tl + 1) (C8 v112) (C8 v120) (C8 v128) (C8 v136) (C8 v144) (Z_to_bv 64 nbs) (Z_to_bv 64 tl))).
    { unfold x2_frame.
      lazymatch type of F1 with rw_cells _ _ _ ?l1 => lazymatch type of NSC with rw_cells _ _ _ ?l2 => lazymatch type of FSAV with rw_cells _ _ _ ?l3 =>
        change (rw_cells psegs m0 (SPV + -272) (l1 ++ l2 ++ l3)) end end end.
      apply rw_cells_app. split; [exact F1|]. cbn [cells_size csize Nat.add]. replace (SPV + -272 + Z.of_nat 160) with (SPV + -112) by lia.
      apply rw_cells_app. split; [exact NSC|]. cbn [cells_size csize Nat.add]. replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact FSAV. }
    clear F1 NSC FSAV.
    (* [comment removed for export] *)
    remember (map (Z_to_bv 8) dt) as dtbs eqn:EDTB.
    assert (DTBL : Z.of_nat (length dtbs) = 16388) by (subst dtbs; rewrite length_map; lia). clear EDTB.
    rewrite <- (firstn_skipn 4 dtbs) in DTC. apply (proj1 (u8arr_app psegs _ _ _ _)) in DTC. destruct DTC as [HDRC CELC].
    assert (HL4 : length (firstn 4 dtbs) = 4%nat) by (rewrite length_firstn; lia).
    rewrite HL4 in CELC. change (DT + Z.of_nat 4) with (DT + 4) in CELC.
    destruct (u16s_of_bytes (Z.to_nat 8192) (skipn 4 dtbs) ltac:(rewrite length_skipn; lia)) as (cw0 & CWL0 & _ & ECW). rewrite ECW in CELC. clear ECW.
    apply rw_cells_of_u8arr in HDRC. rewrite HL4 in HDRC.
    (* [comment removed for export] *)
    pose proof SYC as SYS2. apply rw_cells_of_u8arr in SYS2. apply stk_of_rw_cells in SYS2. cbn [cells_size csize] in SYS2.
    replace (WK + 736 + Z.of_nat (length x13 + 0)) with (WK + 992) in SYS2 by lia.
    assert (WKR2 : stk psegs m0 (WK + 992) (WK + wksz)).
    { apply rw_cells_of_u8arr in HWC. apply stk_of_rw_cells in HWC. cbn [cells_size csize] in HWC. rewrite length_map in HWC.
      apply (stk_merge psegs _ (WK + 992) (WK + 1248) (WK + wksz)); [replace (WK + 1248) with (WK + 992 + Z.of_nat (length hw + 0)) by lia; exact HWC| |lia].
      apply (stk_merge psegs _ (WK + 1248) (WK + 2124) (WK + wksz)); [replace (WK + 2124) with (WK + 1248 + 876) by lia; exact CWK' | exact WKR | lia]. }
    assert (MOD : x2_models rank tl T maxW x38 (Zupd 1 0 x11)).
    { destruct ROWS as (RL & R0M & RCM & _). unfold x2_models. split; [exact RL|]. split; [rewrite Zupd_length; exact RSL3|]. split; [exact R0M|].
      split; [intros c w Hc Hw; apply RCM; lia|].
      intros w Hw. destruct (Z.eq_dec w 1) as [->|NE].
      - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). rewrite (xs1_1 rank). reflexivity.
      - rewrite Znth_Zupd_other by lia. replace w with (w - 1 + 1) at 1 by lia. rewrite (RS3M (w - 1) ltac:(lia)). unfold psort.
        destruct (Z.eqb_spec (w - 1) 0) as [E|_]; [exfalso; lia|].
        pose proof (xs1_step rank (w - 1) ltac:(lia)) as XS. replace (w - 1 + 1) with w in XS by lia. lia. }
    eapply x2_fill with (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rvl := x38) (rs0 := Zupd 1 0 x11)
                        (hdr := firstn 4 dtbs) (cw := cw0) (syb := x13) (hdw := hdw) (h3 := hdw ≫ 24) (r0 := r0); try eassumption; try reflexivity; try lia.
    - unfold x2_geo. repeat (split; [first [assumption | lia]|]). assumption.
    - unfold X2G. split; [exact HDRC|]. split; [split; [exact CELC | lia]|]. split; [exact RVA|]. split; [exact RK|]. split; [exact RSA|].
      split; [exact (proj1 SYC)|]. split; [exact SYL|]. split; [exact SYS2|]. split; [exact WKR2|]. split; [exact FR|]. split; [reflexivity|].
      split; [exact STK'|]. split; [eassumption|]. split; [exact MU | exact WM].
  Qed.

End X2S.
