(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import huf411_kit_x1_defs huf411_kit_x1_build huf411_kit_x1_resc huf411_kit_x1_sort huf411_kit_x1_fill.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)

Section X1.
  Hypothesis RSTATS : huf_rstats_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV SRC n DT WK wksz lo : Z) (src dtb : list byte).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis SRCLEN : Z.of_nat (length src) = n.  Hypothesis SRCL : 4096 <= SRC.  Hypothesis NR : n < 2^32.  Hypothesis SRCH : SRC + n < 2^47.
  Hypothesis HDR : huf_hdr_ok dtb.  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis OFFSRC : SRC + n <= lo \/ SPV <= SRC.  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis DTSRC : DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT.  Hypothesis WKSRC : WK + wksz <= SRC \/ SRC + n <= WK.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Theorem huf_rdx1_body : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    mem_inv usegs m -> stk usegs m lo SPV -> bytes_at usegs m SRC src -> u8arr usegs m DT dtb -> stk usegs m WK (WK + wksz) ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
               (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_RDX1) fc None m (seg_rom usegs)).
  Proof.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK SRCB DTC WKS. unfold PHUF_RDX1.
    pose proof HDR as [DTLEN DT0].
    assert (MU : munch [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)] m m) by apply munch_refl.
    assert (WM : wmono usegs m m) by apply wmono_refl.
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    zstep. carve_frame 240%nat STK.
    do 13 zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 136 ?j :: _) => generalize dependent j; intros fj FR end.
    lazymatch type of FR with rw_cells _ _ _ (CB 136 ?j :: ?post) =>
      apply (rw_cells_split_CB usegs _ _ [] 136 j post [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?k (firstn ?a ?b)] => let j := fresh "fj" in set (j := firstn a b) in FR; clearbody j end.
    clear fj.
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17] rest)) in FR; destruct FR as [F0 FSAV] end.
    cbn [cells_size csize Nat.add] in FSAV. replace (SPV + -240 + Z.of_nat 136) with (SPV + -104) in FSAV by lia.
    zstep. if_cases KC0; zify_cond KC0; [exfalso; lia|].
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 (2^64 - 44)) by (apply bv_eq; reflexivity).
      eapply x1_exit with (dtb' := dtb) (r := 2^64 - 44); try eassumption; try reflexivity; [lia | intros E; vm_compute in E; discriminate E]. }
    zstep. zstep. if_cases KN; zify_cond KN; [exfalso; lia|].
    zstep. zstep. zstep. if_cases KA; zify_cond KA.
    { exfalso. change 3 with (Z.ones 2) in KA. rewrite Z.land_ones in KA by lia. lia. }
    do 12 zstep. zstep.
    (* [comment removed for export] *)
    destruct (stk_split usegs _ WK (WK + 52) (WK + wksz) WKS ltac:(lia)) as [RSS WKS1].
    destruct (stk_split usegs _ (WK + 52) (WK + 104) (WK + wksz) WKS1 ltac:(lia)) as [RTS WKS2].
    destruct (stk_split usegs _ (WK + 104) (WK + 980) (WK + wksz) WKS2 ltac:(lia)) as [STS WKS3].
    destruct (stk_split usegs _ (WK + 980) (WK + 1236) (WK + wksz) WKS3 ltac:(lia)) as [SYS WKS4].
    destruct (stk_split usegs _ (WK + 1236) (WK + 1492) (WK + wksz) WKS4 ltac:(lia)) as [HWS WKR].
    clear WKS WKS1 WKS2 WKS3 WKS4.
    (* [comment removed for export] *)
    lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?rest) =>
      apply (proj1 (rw_cells_app usegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15] rest)) in F0; destruct F0 as [F0 NSC] end.
    cbn [cells_size csize Nat.add] in NSC. replace (SPV + -240 + Z.of_nat 128) with (SPV + -112) in NSC by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mpre end.
    assert (ARGB : bytes_at usegs mpre (SPV + -240) (le8 (Z_to_bv 64 876))).
    { pose proof (SysStep.rw_cells_bytes_at _ _ _ _ F0) as HB. cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. exact (proj1 HB). }
    pose proof NSC as NSS. apply stk_of_rw_cells in NSS. cbn [cells_size csize Nat.add] in NSS. replace (SPV + -112 + Z.of_nat 8) with (SPV + -112 + 8) in NSS by lia.
    clear NSC.
    replace (Z_to_bv 64 (SPV + -108)) with (Z_to_bv 64 (SPV + -112 + 4)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (RSTATS _ gp tp _ _ _ _ _ _ _ _ s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc mpre (SPV + -240) (WK + 1236) WK (SPV + -112) SRC n (WK + 104) 876 lo WK wksz src);
        try eassumption; try lia.
      - replace (WK + 1236 + 256) with (WK + 1492) by lia. exact HWS.
      - replace (WK + 104 + 876) with (WK + 980) by lia. exact STS. }
    unfold huf_rstats_post. post_call usegs mpre.
    lazymatch goal with |- evt _ _ (MS (mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?r) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => rename r into r0 end.
    rename PC into STK'. rename PC0 into STS'. rename PC1 into R0R.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      destruct POST as [(RNE & _) | (RE & HWS' & RSS' & NSS')]; [exfalso; unfold zd_is_error, ZE_maxCode in RNE; apply Z.ltb_ge in RNE; lia|].
      zstep. zstep.
      eapply x1_exit_stk with (dtb' := dtb) (r := r0); try eassumption.
      - apply (stk_merge usegs _ WK (WK + 52) (WK + wksz) RSS'); [|lia].
        apply (stk_merge usegs _ (WK + 52) (WK + 104) (WK + wksz) RTS); [|lia].
        apply (stk_merge usegs _ (WK + 104) (WK + 980) (WK + wksz)); [replace (WK + 980) with (WK + 104 + 876) by lia; exact STS'| |lia].
        apply (stk_merge usegs _ (WK + 980) (WK + 1236) (WK + wksz) SYS); [|lia].
        apply (stk_merge usegs _ (WK + 1236) (WK + 1492) (WK + wksz)); [replace (WK + 1492) with (WK + 1236 + 256) by lia; exact HWS' | exact WKR | lia].
      - apply stk_of_rw_cells in F0. cbn [cells_size csize Nat.add] in F0.
        apply (stk_merge usegs _ (SPV + -240) (SPV + -112) (SPV + -104)); [replace (SPV + -112) with (SPV + -240 + Z.of_nat 128) by lia; exact F0 | | lia].
        replace (SPV + -104) with (SPV + -112 + 8) by lia. exact NSS'.
      - intros E. rewrite RE in E. discriminate E. }
    destruct POST as [(RNE & R0N & hw & rank & tl0 & nbs & HWC & HWLEN & HWBY & RK & NSC & SOK & NBR) | (RE & _)];
      [| exfalso; unfold zd_is_error, ZE_maxCode in RE; apply Z.ltb_lt in RE; lia].
    rewrite <- (bytes_of_unsigned dtb) in DTC.
    remember (map bv_unsigned dtb) as dt eqn:EDT.
    assert (DTL' : Z.of_nat (length dt) = HUF_DTABLE_BYTES) by (subst dt; rewrite length_map; exact DTLEN).
    assert (DTBY : Forall (fun c => 0 <= c < 256) dt) by (subst dt; apply bytes_unsigned_range).
    unfold HUF_DTABLE_BYTES in DTL'.
    assert (DTZ0 : Znth 0 dt = 12).
    { subst dt. unfold Znth. change (Z.to_nat 0) with 0%nat. destruct dtb as [|b0 t]; [discriminate DT0|]. cbn in DT0 |- *. injection DT0 as ->. reflexivity. }
    clear EDT.
    zstep. zstep. if_cases KD; zify_cond KD.
    { exfalso. change 3 with (Z.ones 2) in KD. rewrite Z.land_ones in KD by lia. lia. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let a := cur_mem_addr in
      pose proof (u8_znth4 usegs mm DT dt 0 a (proj1 DTC) DTBY ltac:(lia) ltac:(lia) ltac:(addr_tac)) as RDH end.
    zstep.
    pose proof (Forall_Znth _ dt 0 DTBY ltac:(lia)) as B0. pose proof (Forall_Znth _ dt 1 DTBY ltac:(lia)) as B1.
    pose proof (Forall_Znth _ dt 2 DTBY ltac:(lia)) as B2. pose proof (Forall_Znth _ dt 3 DTBY ltac:(lia)) as B3. cbv beta in B0, B1, B2, B3.
    rewrite DTZ0.
    remember (12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt) as hdw eqn:EHDW.
    assert (HDWR : 0 <= hdw < 2^32 /\ hdw mod 256 = 12) by (subst hdw; clear - B1 B2 B3; Z.div_mod_to_equations; lia).
    clear EHDW RDH.
    rewrite (zx32w_small hdw) by lia.
    zstep.
    replace (Z.land hdw 255) with 12 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; lia).
    zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep. zstep. zstep. zstep. zstep.
    pose proof SOK as (TL0R & _).
    rewrite (zx32w_small nbs) by lia. rewrite (sx32w_small tl0) by lia.
    rewrite (unsigned_lit nbs) by lia. rewrite (swrap32_small (nbs + 0)) by lia. replace (nbs + 0) with nbs by lia.
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
    assert (IM : x1m DT WK wksz SPV lo m [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
                   [C8 (Z_to_bv 64 876); C8 flags; CB 8 fj2; CB 8 fj3; CB 8 fj4; CB 8 fj5; CB 8 fj6; CB 8 fj7; CB 8 fj8; CB 8 fj9;
                    CB 8 fj10; CB 8 fj11; C8 (Z_to_bv 64 WK); CB 8 fj13; CB 8 fj14; CB 8 fj15]
                   (Z_to_bv 64 nbs) (Z_to_bv 64 tl0) dt hw rank mc).
    { unfold x1m, HUF_TBL_STACK, HUF_DTABLE_BYTES.
      replace (WK + 104 + 876) with (WK + 980) in STS' by lia.
      repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    assert (KS : forall hw rank tl, huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl ->
      Z.of_nat (length hw) = 256 -> Forall isbyte hw -> Z.of_nat (length rank) = 13 ->
      forall m2 dt2 rst syb y1 y5 y6 y7 y8 y10 y11 y12 y13 y18 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
       x1s DT WK wksz SPV lo m [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] hw rank
         [C8 (Z_to_bv 64 876); C8 flags; CB 8 fj2; C8 (Z_to_bv 64 r0); CB 8 fj4; CB 8 fj5; C8 (Z_to_bv 64 DT); CB 8 fj7; CB 8 fj8;
          C8 (Z_to_bv 64 (tl + 1)); CB 8 fj10; CB 8 fj11; C8 (Z_to_bv 64 WK); CB 8 fj13; CB 8 fj14; CB 8 fj15]
         (Z_to_bv 64 nbs) (Z_to_bv 64 tl) dt2 rst syb m2 -> x1pref tl 0 dt2 -> (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
       evt usegs POST (MS (mkR y1 (Z_to_bv 64 (SPV + -240)) gp tp y5 y6 y7 y8 (Z_to_bv 64 (WK + 1236)) y10 y11 y12 y13 (Z_to_bv 64 nbs) (Z_to_bv 64 tl)
                              (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 (nbs + -4)) y18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x1eb24) fc None m2 (seg_rom usegs))).
    { intros hw' rank' tl STK1 HWL1 HWB1 RKL1 m2 dt2 rst syb y1 y5 y6 y7 y8 y10 y11 y12 y13 y18 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31 I2 PR2 RS2.
      pose proof STK1 as (TLR & _).
      eapply x1_sort; try eassumption; try lia.
      intros m3 rst' syb' z1 z5 z6 z7 z8 z9 z10 z11 z12 z14 z16 z17 z18 z20 z21 z22 z23 z24 z25 z26 z27 z28 z29 z30 z31 I3.
      eapply x1_fill; try eassumption; try lia. }
    zstep. if_cases K3; zify_cond K3; swap 1 2.
    - (* [comment removed for export] *)
      zstep. if_cases K4; zify_cond K4.
      + (* [comment removed for export] *)
        assert (E11 : tl0 = 11) by lia. subst tl0.
        zstep.
        eapply x1_build; try eassumption; try lia.
        apply KS; first [exact SOK | assumption | lia].
      + (* [comment removed for export] *)
        eapply x1_rescale; try eassumption; try lia.
        intros m2 hw' rank' y1 y5 y6 y7 y11 y12 y13 y16 y17 y21 y22 y23 y24 y25 y26 y27 y29 y30 y31 I2 SOK2.
        pose proof I2 as (_ & _ & _ & _ & HWL2 & HWB2 & _ & RKL2 & _).
        eapply x1_build; try eassumption; try lia.
        apply KS; assumption.
    - (* [comment removed for export] *)
      eapply x1_build; try eassumption; try lia.
      apply KS; first [exact SOK | assumption | lia].
  Qed.
End X1.

(* [comment removed for export] *)
Theorem huf_rdx1_proof : huf_rstats_stmt -> huf_rdx1_stmt.
Proof.
  intros RSTATS. unfold huf_rdx1_stmt, huf_rd_stmt_at. intros.
  eapply (huf_rdx1_body RSTATS); eassumption.
Qed.
