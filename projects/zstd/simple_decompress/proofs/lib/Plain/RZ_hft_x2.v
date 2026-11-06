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
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_bdt_defs RZ_hft_x2_defs RZ_hft_x2_gdefs RZ_hft_x2_pre RZ_hft_x2_wl RZ_hft_x2_setup.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X2.
  Hypothesis RSTATS : huf_rstats_stmt.
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
  Theorem huf_rdx2_body : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    mem_inv psegs m -> stk psegs m lo SPV -> bytes_at psegs m SRC src -> u8arr psegs m DT dtb -> stk psegs m WK (WK + wksz) ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
               (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_RDX2) fc None m (seg_rom psegs)).
  Proof.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK SRCB DTC WKS. unfold PHUF_RDX2.
    pose proof HDR as [DTLEN DT0]. unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    assert (MU : munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 1024, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    zstep. carve_frame 272%nat STK.
    do 13 zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 168 ?j :: _) => generalize dependent j; intros fj FR end.
    lazymatch type of FR with rw_cells _ _ _ (CB 168 ?j :: ?post) =>
      apply (rw_cells_split_CB psegs _ _ [] 168 j post [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 4; 4]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?k (firstn ?a ?b)] => let j := fresh "fj" in set (j := firstn a b) in FR; clearbody j end.
    clear fj.
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: ?c21 :: ?rest) =>
      apply (proj1 (rw_cells_app psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20; c21] rest)) in FR; destruct FR as [F0 FSAV] end.
    cbn [cells_size csize Nat.add] in FSAV. replace (SPV + -272 + Z.of_nat 168) with (SPV + -104) in FSAV by lia.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    2:{ (* [comment removed for export] *)
        zstep. zstep.
        replace (Z_to_bv 64 (-1)) with (Z_to_bv 64 18446744073709551615) by (apply bv_eq; reflexivity).
        apply stk_of_rw_cells in F0. cbn [cells_size csize Nat.add] in F0.
        eapply x2_exit_err with (dtb' := dtb) (r := 18446744073709551615); try eassumption; try reflexivity; try lia.
        replace (SPV + -104) with (SPV + -272 + Z.of_nat 168) by lia. exact F0. }
    assert (WK2124 : 2124 <= wksz) by (rewrite Z.shiftr_div_pow2 in K0 by lia; change (2^2) with 4 in K0; Z.div_mod_to_equations; lia).
    clear K0.
    rewrite <- (bytes_of_unsigned dtb) in DTC.
    remember (map bv_unsigned dtb) as dt eqn:EDT.
    assert (DTL' : Z.of_nat (length dt) = 16388) by (subst dt; rewrite length_map; exact DTLEN).
    assert (DTBY : Forall (fun c => 0 <= c < 256) dt) by (subst dt; apply bytes_unsigned_range).
    assert (DTZ0 : Znth 0 dt = 12).
    { subst dt. unfold Znth. change (Z.to_nat 0) with 0%nat. destruct dtb as [|b0 t]; [discriminate DT0|]. cbn in DT0 |- *. injection DT0 as ->. reflexivity. }
    clear EDT.
    do 4 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let a := cur_mem_addr in
      pose proof (u8_znth4 psegs mm DT dt 0 a (proj1 DTC) DTBY ltac:(lia) ltac:(lia) ltac:(addr_tac)) as RDH end.
    zstep.
    pose proof (Forall_Znth _ dt 1 DTBY ltac:(lia)) as B1. pose proof (Forall_Znth _ dt 2 DTBY ltac:(lia)) as B2. pose proof (Forall_Znth _ dt 3 DTBY ltac:(lia)) as B3. cbv beta in B1, B2, B3.
    rewrite DTZ0.
    remember (12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt) as hdw eqn:EHDW.
    assert (HDWR : 0 <= hdw < 4294967296 /\ hdw mod 256 = 12) by (subst hdw; clear - B1 B2 B3; Z.div_mod_to_equations; lia).
    clear EHDW RDH.
    rewrite (zx32w_small hdw) by lia.
    zstep.
    replace (Z.land hdw 255) with 12 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; lia).
    do 4 zstep. zstep.
    (* [comment removed for export] *)
    destruct (stk_split psegs _ WK (WK + 624) (WK + wksz) WKS ltac:(lia)) as [RVS WKS1].
    destruct (stk_split psegs _ (WK + 624) (WK + 736) (WK + wksz) WKS1 ltac:(lia)) as [RSS WKS2].
    destruct (stk_split psegs _ (WK + 736) (WK + 992) (WK + wksz) WKS2 ltac:(lia)) as [SYS WKS3].
    destruct (stk_split psegs _ (WK + 992) (WK + 1248) (WK + wksz) WKS3 ltac:(lia)) as [HWS WKS4].
    destruct (stk_split psegs _ (WK + 1248) (WK + 2124) (WK + wksz) WKS4 ltac:(lia)) as [CWK WKR].
    clear WKS WKS1 WKS2 WKS3 WKS4.
    destruct (stk_open psegs _ (WK + 624) (WK + 736) (WK + 624) 112%nat RSS ltac:(lia) ltac:(lia)) as (jr & RSC & _ & _).
    eapply evt_cut.
    { eapply (memset_spec _ _ gp tp _ _ _ _ _ (Z_to_bv 64 (WK + 624)) (Z_to_bv 64 0) (Z_to_bv 64 112) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ jr); [|eassumption].
      rewrite !unsigned_lit by lia. exact RSC. }
    unfold memset_post. rewrite !unsigned_lit by lia.
    lazymatch goal with MIx : mem_inv psegs ?mm |- _ => post_call psegs mm end.
    apply u8arr_of_rw_cells in POST.
    replace (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat 112)) with (repeat (Z_to_bv 8 0) 52 ++ u32s (map (Z_to_bv 64) (repeat 0 15))) in POST
      by (rewrite u32s_zeros; change (4 * 15)%nat with 60%nat; rewrite <- repeat_app; reflexivity).
    apply (proj1 (u8arr_app psegs _ _ _ _)) in POST. destruct POST as [RSZ RS0A].
    rewrite repeat_length in RS0A. replace (WK + 624 + Z.of_nat 52) with (WK + 676) in RS0A by lia.
    apply u32arr_of_u32s in RS0A.
    remember (repeat 0 15) as rs00 eqn:ERS00. assert (RS00L : Z.of_nat (length rs00) = 15) by (subst rs00; reflexivity). clear ERS00.
    apply rw_cells_of_u8arr in RSZ. apply stk_of_rw_cells in RSZ. cbn [cells_size csize] in RSZ. rewrite repeat_length in RSZ.
    replace (WK + 624 + Z.of_nat (52 + 0)) with (WK + 624 + 52) in RSZ by lia.
    zstep. zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    do 6 zstep. zstep. zstep. do 4 zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?rest) =>
      apply (proj1 (rw_cells_app psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19] rest)) in F0; destruct F0 as [F0 NSC] end.
    cbn [cells_size csize Nat.add] in NSC. replace (SPV + -272 + Z.of_nat 160) with (SPV + -112) in NSC by lia.
    assert (ARGB : bytes_at psegs m1 (SPV + -272) (le8 (Z_to_bv 64 876))).
    { pose proof (SysStep.rw_cells_bytes_at _ _ _ _ F0) as HB. cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. exact (proj1 HB). }
    pose proof NSC as NSS. apply stk_of_rw_cells in NSS. cbn [cells_size csize Nat.add] in NSS. replace (SPV + -112 + Z.of_nat 8) with (SPV + -112 + 8) in NSS by lia.
    clear NSC.
    replace (Z_to_bv 64 (SPV + -108)) with (Z_to_bv 64 (SPV + -112 + 4)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (RSTATS _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 (SPV + -272) (WK + 992) (WK + 624) (SPV + -112) SRC n (WK + 1248) 876 lo WK wksz src);
        try eassumption; try lia.
      - replace (WK + 992 + 256) with (WK + 1248) by lia. exact HWS.
      - replace (WK + 1248 + 876) with (WK + 2124) by lia. exact CWK. }
    unfold huf_rstats_post. post_call psegs m1.
    rename x28 into r0. rename PC into STK'. rename PC0 into CWK'. rename PC1 into R0R.
    zstep. zstep. if_cases K2; zify_cond K2.
    { (* [comment removed for export] *)
      destruct POST as [(RNE & _) | (RE & HWS' & RSS' & NSS')]; [exfalso; unfold zd_is_error, ZE_maxCode in RNE; apply Z.ltb_ge in RNE; lia|].
      zstep. zstep.
      eapply x2_exit_err with (dtb' := map (Z_to_bv 8) dt) (r := r0); try eassumption.
      - split; [rewrite length_map; exact DTL'|]. rewrite <- DTZ0. apply (nth_error_map_Znth (Z_to_bv 8) dt 0). lia.
      - apply u8arr_of_u32arr in RS0A. apply rw_cells_of_u8arr in RS0A. apply stk_of_rw_cells in RS0A. cbn [cells_size csize] in RS0A.
        rewrite u32s_length, length_map in RS0A.
        apply (stk_merge psegs _ WK (WK + 624) (WK + wksz) RVS); [|lia].
        apply (stk_merge psegs _ (WK + 624) (WK + 676) (WK + wksz)); [replace (WK + 676) with (WK + 624 + 52) by lia; exact RSS'| |lia].
        apply (stk_merge psegs _ (WK + 676) (WK + 736) (WK + wksz)); [replace (WK + 736) with (WK + 676 + Z.of_nat (4 * length rs00 + 0)) by lia; exact RS0A| |lia].
        apply (stk_merge psegs _ (WK + 736) (WK + 992) (WK + wksz) SYS); [|lia].
        apply (stk_merge psegs _ (WK + 992) (WK + 1248) (WK + wksz)); [replace (WK + 1248) with (WK + 992 + 256) by lia; exact HWS'| |lia].
        apply (stk_merge psegs _ (WK + 1248) (WK + 2124) (WK + wksz)); [replace (WK + 2124) with (WK + 1248 + 876) by lia; exact CWK' | exact WKR | lia].
      - apply stk_of_rw_cells in F0. cbn [cells_size csize Nat.add] in F0.
        apply (stk_merge psegs _ (SPV + -272) (SPV + -112) (SPV + -104)); [replace (SPV + -112) with (SPV + -272 + Z.of_nat 160) by lia; exact F0 | | lia].
        replace (SPV + -104) with (SPV + -112 + 8) by lia. exact NSS'. }
    destruct POST as [(RNE & R0N & hw & rank & tl & nbs & HWC & HWLEN & HWBY & RK & NSC & SOK & NBR) | (RE & _)];
      [| exfalso; unfold zd_is_error, ZE_maxCode in RE; apply Z.ltb_lt in RE; lia].
    pose proof SOK as (TLR & _).
    zstep. rewrite (sx32w_small tl) by lia.
    zstep. if_cases K3; zify_cond K3; [exfalso; lia|].
    assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
    do 16 zstep.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (tl - tl)) by (f_equal; lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply x2_maxw_loop with (j := Z.to_nat tl) (ws := firstn (Z.to_nat nbs) hw) (rank := rank) (tl := tl) (T := if tl <? 12 then 11 else 12) (v := tl); try eassumption; try lia end.
    { destruct (tl <? 12) eqn:E; [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; lia. }
    intros maxW y16 MAXW HIGH.
    zstep.
    pose proof SOK as (TLR2 & _).
    destruct (tl <? 12) eqn:ETL; [apply Z.ltb_lt in ETL | apply Z.ltb_ge in ETL]; change (0 <? 1) with true; cbn [Z.b2z]; [change (Z.land 1 1) with 1 | change (Z.land 0 1) with 0].
    - if_cases KT; zify_cond KT; [exfalso; lia|].
      zstep.
      eapply x2_setup with (SRC := SRC) (n := n) (src := src) (dt := dt) (hw := hw) (rank := rank) (rs00 := rs00) (tl := tl) (T := 11) (maxW := maxW) (nbs := nbs) (r0 := r0) (hdw := hdw); try eassumption; try lia.
    - if_cases KT; zify_cond KT; [|exfalso; lia].
      eapply x2_setup with (SRC := SRC) (n := n) (src := src) (dt := dt) (hw := hw) (rank := rank) (rs00 := rs00) (tl := tl) (T := 12) (maxW := maxW) (nbs := nbs) (r0 := r0) (hdw := hdw); try eassumption; try lia.
  Qed.
End X2.

(* [comment removed for export] *)
Theorem huf_rdx2_proof : huf_rstats_stmt -> huf_rdx2_stmt.
Proof.
  intros RSTATS. unfold huf_rdx2_stmt, huf_rd_stmt_at. intros.
  eapply (huf_rdx2_body RSTATS); eassumption.
Qed.
