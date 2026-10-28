(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_pre RZ_hft_x2_wl huf421_kit_fill huf411_kit_rs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac c8ify H :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?l =>
    let rec go pre l :=
      lazymatch l with
      | CB 8 ?j :: ?post =>
          let H' := fresh "H" in
          destruct (cb8_as_c8 sg mm A pre j post H) as [? H']; cbn [app] in H'; clear H; rename H' into H; c8ify H
      | CB ?k ?j :: ?post =>
          let k' := eval compute in (k - 8)%nat in
          let H' := fresh "H" in
          pose proof (rw_cells_split_CB sg mm A pre k j post [8%nat; k'] H eq_refl) as H';
          cbn [mk_CB_cells app] in H'; clear H; rename H' into H; c8ify H
      | ?c :: ?l' => go (pre ++ [c]) l'
      | nil => idtac
      end
    in go (@nil cell) l
  end.

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
  Hypothesis DTA : rsk_al DT 4.  Hypothesis FILLW : huf_fillw_stmt.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo true m).
  Notation MUNCH := [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)].
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -400)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma x2_setup_e : forall m2 (dt hw rank rs rvl : list Z) (syb : list byte) (tl T maxW nbs r0 h3 : Z)
      flags w16 w48 w56 w64 w72 w88 k136 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280
      x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30,
    mem_inv usegs m2 -> munch MUNCH m m2 -> wmono usegs m m2 ->
    u8arr usegs m2 DT (map (Z_to_bv 8) dt) -> Z.of_nat (length dt) = 16388 -> 0 <= h3 < 256 ->
    u32arr usegs m2 WK (map (Z_to_bv 64) rvl) -> x2_models rank tl T maxW rvl (Zupd 1 0 rs) ->
    u32arr usegs m2 (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr usegs m2 (WK + 676) (map (Z_to_bv 64) (Zupd 1 0 rs)) ->
    u8arr usegs m2 (WK + 736) syb -> Z.of_nat (length syb) = 256 ->
    u8arr usegs m2 (WK + 992) (map (Z_to_bv 8) hw) -> Z.of_nat (length hw) = 256 ->
    stk usegs m2 (WK + 1248) (WK + 1248 + 876) -> stk usegs m2 (WK + 2124) (WK + wksz) -> 2124 <= wksz ->
    rw_cells usegs m2 (SPV + -400)
      [C8 (Z_to_bv 64 876); C8 flags; C8 w16; C8 (Z_to_bv 64 (h3 * 16777216)); C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 DT);
       C8 w48; C8 w56; C8 w64; C8 w72; C8 (Z_to_bv 64 12); C8 w88; C8 (Z_to_bv 64 (tl + 1 - maxW)); C8 (Z_to_bv 64 (tl + 1));
       C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 (WK + 676));
       C8 k136; C8 k144; C8 k152; C8 k160; C8 k168; C8 k176; C8 k184; C8 k192; C8 k200; C8 k208; C8 k216; C8 k224;
       C8 k232; C8 k240; C8 k248; C8 k256; C8 k264; C8 k272; C8 k280; C4 (Z_to_bv 64 nbs); C4 (Z_to_bv 64 tl);
       C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m2 lo (SPV + -400) ->
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= r0 <= n ->
    tl <= T <= 12 -> 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
    evt usegs POST (STF 0x1f698 m2 (Z_to_bv 64 T) x5 x6 x7 (Z_to_bv 64 maxW) x9 (Z_to_bv 64 ((maxW + 1) ≪ 32)) x11 x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (DT + 4)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 (Z_to_bv 64 tl)).
  Proof using LO0 LOS SPR DTL DTH DTAL WKL WKSZ WKH WKAL OFFDT OFFWK DTWK NR DTA FILLW.
    clear SRCLEN SRCL SRCH HDR OFFSRC DTSRC WKSRC.
    intros until x30; intros MI MU WM DTC DTL' H3R RVA MOD RK RSA SYC SYL HWC HWLEN CWK' WKR WK2124 FR STK' SOK R0N TT MAXW HIGH.
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof SOK as (TLR & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    pose proof MOD as (RVLEN & RSLEN & _).
    remember (map (Z_to_bv 8) dt) as dtbs eqn:EDTB.
    assert (DTBL : Z.of_nat (length dtbs) = 16388) by (subst dtbs; rewrite length_map; lia). clear EDTB.
    rewrite <- (firstn_skipn 4 dtbs) in DTC. apply (proj1 (u8arr_app usegs _ _ _ _)) in DTC. destruct DTC as [HDRC CELC].
    assert (HL4 : length (firstn 4 dtbs) = 4%nat) by (rewrite length_firstn; lia).
    rewrite HL4 in CELC. change (DT + Z.of_nat 4) with (DT + 4) in CELC.
    destruct (u16s_of_bytes (Z.to_nat 8192) (skipn 4 dtbs) ltac:(rewrite length_skipn; lia)) as (cw0 & CWL0 & _ & ECW). rewrite ECW in CELC. clear ECW.
    apply rw_cells_of_u8arr in HDRC. rewrite HL4 in HDRC.
    pose proof SYC as SYS2. apply rw_cells_of_u8arr in SYS2. apply stk_of_rw_cells in SYS2. cbn [cells_size csize] in SYS2.
    replace (WK + 736 + Z.of_nat (length syb + 0)) with (WK + 992) in SYS2 by lia.
    pose proof (proj1 SYC) as SYB. clear SYC.
    assert (WKR2 : stk usegs m2 (WK + 992) (WK + wksz)).
    { apply rw_cells_of_u8arr in HWC. apply stk_of_rw_cells in HWC. cbn [cells_size csize] in HWC. rewrite length_map in HWC.
      apply (stk_merge usegs _ (WK + 992) (WK + 1248) (WK + wksz)); [replace (WK + 1248) with (WK + 992 + Z.of_nat (length hw + 0)) by lia; exact HWC| |lia].
      apply (stk_merge usegs _ (WK + 1248) (WK + 2124) (WK + wksz)); [replace (WK + 2124) with (WK + 1248 + 876) by lia; exact CWK' | exact WKR | lia]. }
    clear HWC CWK' WKR.
    zstep. if_cases K0; [exfalso; zify_cond K0; repeat (rewrite Z.mod_small in K0 by lia); lia|]. try clear K0.
    zstep. zstep. rewrite (swrap32_small (tl + 1 - T)) by lia.
    do 8 zstep.
    zstep. replace (tl ≪ 1) with (2 * tl) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep. rewrite (Z.mod_small (maxW + 1)) by lia.
    do 6 zstep.
    zstep. rewrite (swrap32_small (2 * tl + 1 - T)) by lia.
    do 5 zstep.
    lazymatch goal with FRx : rw_cells usegs ?mm (SPV + -400) _ |- _ =>
      replace (Z_to_bv 64 (Z.lxor (DT + 4) 18446744073709551615)) with (Z_to_bv 64 (- (DT + 4) - 1)) in FRx
        by (apply Z_to_bv_eqm; rewrite zb_lxor_ones by lia; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia);
      assert (FR2 : rw_cells usegs mm (SPV + -400)
        (x2_frame ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 SPV DT WK tl T maxW (Z_to_bv 64 876) flags w16 (Z_to_bv 64 (h3 * 16777216)) r0
                  k136 k144 k152 k160 (Z_to_bv 64 (2 * tl + 1)) k176 k184 k192 k200 k208 k216 k224 k240 k248 k264 k272 k280 (Z_to_bv 64 nbs) (Z_to_bv 64 tl)))
        by (unfold x2_frame; exact FRx); clear FRx end.
    assert (GEO : x2_geo SPV lo DT WK wksz) by (unfold x2_geo; lia).
    eapply x2_fill with (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rvl := rvl) (rs0 := Zupd 1 0 rs) (r0 := r0) (h3 := h3)
        (c0 := Z_to_bv 64 876) (c8 := flags) (c16 := w16) (hdr3 := Z_to_bv 64 (h3 * 16777216)) (wn := Z_to_bv 64 nbs) (wt := Z_to_bv 64 tl)
        (hdr := firstn 4 dtbs) (cw := cw0) (syb := syb).
    all: try first [ eassumption | reflexivity | lia ].
    all: unfold X2G; repeat (split; [first [eassumption | reflexivity | split; [eassumption | lia]] |]); first [eassumption | reflexivity].
  Qed.


  Lemma x2_setup_de : forall m1 (dt hw rank rs rvl : list Z) (syb : list byte) (tl T maxW nbs r0 h3 : Z) flags fj16 j48 j88 j136
      x5 x6 x9 x11 x12 x13 x15 x16 x17 x20 x21 x22 x24 x25 x26 x27 x29 x30,
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 ->
    u8arr usegs m1 DT (map (Z_to_bv 8) dt) -> Z.of_nat (length dt) = 16388 -> 0 <= h3 < 256 ->
    u32arr usegs m1 WK (map (Z_to_bv 64) rvl) -> Z.of_nat (length rvl) = 156 -> (forall w, 1 <= w <= maxW -> Znth w rvl = rv0 rank tl T w) ->
    u32arr usegs m1 (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr usegs m1 (WK + 676) (map (Z_to_bv 64) (Zupd 1 0 rs)) -> Z.of_nat (length rs) = 15 ->
    (forall w, 0 <= w <= maxW -> Znth (w + 1) rs = psort rank maxW w + Znth w rank) ->
    u8arr usegs m1 (WK + 736) syb -> Z.of_nat (length syb) = 256 ->
    u8arr usegs m1 (WK + 992) (map (Z_to_bv 8) hw) -> Z.of_nat (length hw) = 256 ->
    stk usegs m1 (WK + 1248) (WK + 1248 + 876) -> stk usegs m1 (WK + 2124) (WK + wksz) -> 2124 <= wksz ->
    rw_cells usegs m1 (SPV + -400)
      [C8 (Z_to_bv 64 876); C8 flags; CB 8 fj16; C8 (Z_to_bv 64 (h3 * 16777216)); C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 DT); CB 32 j48;
       C8 (Z_to_bv 64 12); CB 16 j88; C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 WK); C8 (Z_to_bv 64 (- WK - 1)); C8 (Z_to_bv 64 (WK + 676)); CB 152 j136] ->
    rw_cells usegs m1 (SPV + -112) [C4 (Z_to_bv 64 nbs); C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SPV + -104) SAVED -> stk usegs m1 lo (SPV + -400) ->
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 1 <= r0 <= n ->
    tl <= T <= 12 -> 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
    evt usegs POST (STF 0x1f5dc m1 (Z_to_bv 64 T) x5 x6 (Z_to_bv 64 (Z.lxor WK 18446744073709551615)) (Z_to_bv 64 maxW) x9
                        (Z_to_bv 64 ((maxW + 1) ≪ 32)) x11 x12 x13 (Z_to_bv 64 (T - tl + maxW)) x15 x16 x17 (Z_to_bv 64 (WK + 736)) (Z_to_bv 64 (DT + 4))
                        x20 x21 x22 (Z_to_bv 64 WK) x24 x25 x26 x27 (Z_to_bv 64 (tl + 1 - maxW)) x29 x30 (Z_to_bv 64 tl)).
  Proof using LO0 LOS SPR DTL DTH DTAL WKL WKSZ WKH WKAL OFFDT OFFWK DTWK NR DTA FILLW.
    clear SRCLEN SRCL SRCH HDR OFFSRC DTSRC WKSRC.
    intros until x30; intros MI MU WM DTC DTL' H3R RVA RVL RV0 RK RSA RSL RS3M SYC SYL HWC HWLEN CWK' WKR WK2124 F0 NSC FSAV STK' SOK R0N TT MAXW HIGH.
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof SOK as (TLR & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    assert (RSL' : Z.of_nat (length (Zupd 1 0 rs)) = 15) by (rewrite Zupd_length; exact RSL).
    assert (RS0M : forall w, 1 <= w <= maxW + 1 -> Znth w (Zupd 1 0 rs) = xs1 rank w).
    { intros w Hw. destruct (Z.eq_dec w 1) as [->|NE].
      - rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; lia). rewrite (xs1_1 rank). reflexivity.
      - rewrite Znth_Zupd_other by lia. replace w with (w - 1 + 1) at 1 by lia. rewrite (RS3M (w - 1) ltac:(lia)). unfold psort.
        destruct (Z.eqb_spec (w - 1) 0) as [E|_]; [exfalso; lia|].
        pose proof (xs1_step rank (w - 1) ltac:(lia)) as XS. replace (w - 1 + 1) with w in XS by lia. lia. }
    clear RS3M.
    c8ify F0.
    lazymatch type of F0 with rw_cells _ _ _ ?l1 => lazymatch type of NSC with rw_cells _ _ _ ?l2 => lazymatch type of FSAV with rw_cells _ _ _ ?l3 =>
      assert (FR : rw_cells usegs m1 (SPV + -400) (l1 ++ l2 ++ l3)) end end end.
    { apply rw_cells_app. split; [exact F0|]. cbn [cells_size csize Nat.add]. replace (SPV + -400 + Z.of_nat 288) with (SPV + -112) by lia.
      apply rw_cells_app. split; [exact NSC|]. cbn [cells_size csize Nat.add]. replace (SPV + -112 + Z.of_nat 8) with (SPV + -104) by lia. exact FSAV. }
    cbn [app] in FR. clear F0 NSC FSAV.
    zstep.
    zstep. if_cases KR; zify_cond KR; repeat (rewrite Z.mod_small in KR by lia).
    - assert (MOD : x2_models rank tl T maxW rvl (Zupd 1 0 rs)).
      { unfold x2_models. split; [exact RVL|]. split; [exact RSL'|]. split; [exact RV0|]. split; [intros c w Hc Hw; lia | exact RS0M]. }
      eapply x2_setup_e; eassumption.
    - zstep. zstep. zstep. rewrite (Z.mod_small (tl + 1 - maxW)) by lia.
      zstep.
      eapply evt_cut.
      { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
          eapply x2_p5_loop with (WK := WK) (m0 := mm) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := T) (maxW := maxW) (rvl := rvl)
                                 (c := tl + 1 - maxW) (j := Z.to_nat (T - (tl + 1 - maxW) + 1 - (tl + 1 - maxW))) end.
        all: try first [ reflexivity | eassumption | lia | apply munch_refl | apply wmono_refl | (f_equal; lia) ].
        unfold rows_inv. split; [exact RVL|]. split; [exact RV0|]. split; intros; lia. }
      unfold x2_p5_post.
      lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
      rename POST into ROWS. rename PC into RVA5.
      lazymatch type of RVA5 with u32arr _ _ WK (map _ ?rv) => assert (MOD : x2_models rank tl T maxW rv (Zupd 1 0 rs)) end.
      { destruct ROWS as (RL & R0M & RCM & _). unfold x2_models. split; [exact RL|]. split; [exact RSL'|]. split; [exact R0M|].
        split; [intros c w Hc Hw; apply RCM; lia | exact RS0M]. }
      eapply x2_setup_e; eassumption.
  Qed.

End X2S.
