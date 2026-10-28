(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_pre RZ_hft_x2_wl huf421_kit_fill huf411_kit_rs huf42_4_kit_sde.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac cb_split H j sz :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?l =>
    let rec go pre l :=
      lazymatch l with
      | CB ?k j :: ?post =>
          let H' := fresh "H" in
          pose proof (rw_cells_split_CB sg mm A pre k j post sz H eq_refl) as H';
          cbn [mk_CB_cells app] in H'; clear H; rename H' into H
      | ?c :: ?l' => go (pre ++ [c]) l'
      end
    in go (@nil cell) l
  end.

Ltac cb_c8 H j :=
  lazymatch type of H with rw_cells ?sg ?mm ?A ?l =>
    let rec go pre l :=
      lazymatch l with
      | CB 8 j :: ?post =>
          let H' := fresh "H" in
          destruct (cb8_as_c8 sg mm A pre j post H) as [? H']; cbn [app] in H'; clear H; rename H' into H
      | ?c :: ?l' => go (pre ++ [c]) l'
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

  Lemma x2_setup_bc : forall m1 (dt hw rank rs0 : list Z) (tl T maxW nbs r0 h3 : Z) flags fj16 j40 j88 j112 j136
      x5 x6 x9 x12 x16 x18 x21 x24 x25 x26 x27 x28 x29 x30,
    mem_inv usegs m1 -> munch MUNCH m m1 -> wmono usegs m m1 ->
    u8arr usegs m1 DT (map (Z_to_bv 8) dt) -> Z.of_nat (length dt) = 16388 -> 0 <= h3 < 256 ->
    stk usegs m1 WK (WK + 624) -> u32arr usegs m1 (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr usegs m1 (WK + 676) (map (Z_to_bv 64) rs0) -> Z.of_nat (length rs0) = 15 ->
    (forall w, 1 <= w <= maxW -> Znth (w + 1) rs0 = xs1 rank w) ->
    stk usegs m1 (WK + 736) (WK + 992) ->
    u8arr usegs m1 (WK + 992) (map (Z_to_bv 8) hw) -> Z.of_nat (length hw) = 256 -> Forall (fun c => 0 <= c < 256) hw ->
    stk usegs m1 (WK + 1248) (WK + 1248 + 876) -> stk usegs m1 (WK + 2124) (WK + wksz) -> 2124 <= wksz ->
    rw_cells usegs m1 (SPV + -400)
      [C8 (Z_to_bv 64 876); C8 flags; CB 8 fj16; C8 (Z_to_bv 64 (h3 * 16777216)); C8 (Z_to_bv 64 r0); CB 40 j40; C8 (Z_to_bv 64 12);
       CB 16 j88; C8 (Z_to_bv 64 (tl + 1)); CB 16 j112; C8 (Z_to_bv 64 (WK + 676)); CB 152 j136] ->
    rw_cells usegs m1 (SPV + -112) [C4 (Z_to_bv 64 nbs); C4 (Z_to_bv 64 tl)] ->
    rw_cells usegs m1 (SPV + -104) SAVED -> stk usegs m1 lo (SPV + -400) ->
    huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 -> 1 <= r0 <= n ->
    tl <= T <= 12 -> 1 <= maxW <= tl -> (forall u, maxW < u <= 12 -> Znth u rank = 0) ->
    evt usegs POST (STF 0x1f508 m1 (Z_to_bv 64 T) x5 x6 (Z_to_bv 64 (xs1 rank (maxW + 1))) (Z_to_bv 64 maxW) x9
                        (Z_to_bv 64 ((maxW + 1) ≪ 32)) (Z_to_bv 64 (tl - maxW)) x12 (Z_to_bv 64 (WK + 680))
                        (Z_to_bv 64 (Z.lxor (WK + 680) 18446744073709551615)) (Z_to_bv 64 (maxW + 1)) x16 (Z_to_bv 64 (4 * (maxW + 1)))
                        x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 (WK + 992)) x21 (Z_to_bv 64 DT) (Z_to_bv 64 WK) x24 x25 x26 x27
                        x28 x29 x30 (Z_to_bv 64 tl)).
  Proof using LO0 LOS SPR DTL DTH DTAL WKL WKSZ WKH WKAL OFFDT OFFWK DTWK NR DTA FILLW.
    clear SRCLEN SRCL SRCH HDR OFFSRC DTSRC WKSRC.
    intros until x30; intros MI MU WM DTC DTL' H3R RVS RK RSA RSL RS2M SYS HWC HWLEN HWBY CWK' WKR WK2124 F0 NSC FSAV STK' SOK NBR R0N TT MAXW HIGH.
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof SOK as (TLR & _).
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    pose proof (xs1_nonneg (firstn (Z.to_nat nbs) hw) rank tl SOK (maxW + 1) ltac:(lia)) as XT0.
    pose proof (xs1_total (firstn (Z.to_nat nbs) hw) rank tl SOK maxW ltac:(lia) HIGH) as XTT.
    pose proof (st_rank_nonneg (firstn (Z.to_nat nbs) hw) rank tl SOK 0 ltac:(lia)) as CNTZ.
    assert (WSL : FseNCount.Zlength (firstn (Z.to_nat nbs) hw) = nbs) by (unfold FseNCount.Zlength; rewrite length_firstn; lia).
    cb_split F0 j40 [8; 32]%nat. cb_c8 F0 (firstn 8 j40).
    cb_split F0 j112 [8; 8]%nat. cb_c8 F0 (firstn 8 j112). cb_c8 F0 (firstn 8 (skipn 8 j112)).
    zstep. replace ((maxW + 1) ≪ 2) with (4 * (maxW + 1)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    u32w RSA 1 (xs1 rank (maxW + 1)) (xs1 rank (maxW + 1)).
    zstep. if_cases K; zify_cond K; [kchk K|]. try clear K.
    zstep. rewrite (zx32w_small nbs) by lia.
    zstep.
    u32w RSA (maxW + 2) (xs1 rank (maxW + 1)) (xs1 rank (maxW + 1)).
    zstep.
    zstep. if_cases K; zify_cond K; [exfalso; lia|]. try clear K.
    do 5 zstep.
    destruct (stk_open usegs _ (WK + 736) (WK + 992) (WK + 736) 256%nat SYS ltac:(lia) ltac:(lia)) as (sy0 & SYC & _ & _).
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
    unfold x2_p3_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    rename POST into RS3M. rename PC into RSA. rename PC0 into RSL3. rename PC1 into SYC. rename PC2 into SYL.
    clear RSL RS2M.
    zstep. zstep.
    u32w RSA 1 0 0.
    zstep.
    rewrite (swrap32_small (tl - maxW + 1)) by lia. replace (tl - maxW + 1) with (tl + 1 - maxW) by lia.
    rewrite (swrap32_small (T - (tl - maxW))) by lia. replace (T - (tl - maxW)) with (T - tl + maxW) by lia.
    zstep. zstep. zstep.
    lazymatch goal with FRx : rw_cells usegs ?mm (SPV + -400) _ |- _ =>
      replace (Z_to_bv 64 (Z.lxor WK 18446744073709551615)) with (Z_to_bv 64 (- WK - 1)) in FRx
        by (apply Z_to_bv_eqm; rewrite zb_lxor_ones by lia; change (2^64) with 18446744073709551616; Z.div_mod_to_equations; lia) end.
    zstep. if_cases K; zify_cond K; [exfalso; lia|]. try clear K.
    zstep. zstep. rewrite (swrap32_small (T - tl)) by lia.
    zstep. zstep. rewrite (zext32_sh30 (maxW + 1)) by lia.
    zstep. zstep.
    destruct (u32arr_of_stk usegs _ WK 156%nat ltac:(replace (WK + 4 * Z.of_nat 156) with (WK + 624) by lia; exact RVS) ltac:(lia)) as (rvl0 & RVA & RVL0).
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
    unfold x2_p4_post. lazymatch goal with MIx : mem_inv usegs ?mm |- _ => post_call usegs mm end.
    rename POST into RV4M. rename PC into RVA. rename PC0 into RVL4.
    lazymatch type of RSA with u32arr _ _ _ (map _ (Zupd 1 0 ?r)) =>
    lazymatch type of RVA with u32arr _ _ _ (map _ ?rv) =>
    lazymatch type of SYC with u8arr _ _ _ ?sb =>
      eapply x2_setup_de with (dt := dt) (hw := hw) (rank := rank) (rs := r) (rvl := rv) (syb := sb) (tl := tl) (T := T) (maxW := maxW)
                              (nbs := nbs) (r0 := r0) (h3 := h3) end end end.
    all: first [ eassumption | lia ].
  Qed.

End X2S.
