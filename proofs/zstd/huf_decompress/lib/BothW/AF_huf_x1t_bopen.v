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
     AH_huf_rdt2 AF_huf_dec_iface AF_huf_x1t_top AF_huf_x1t_bseg AF_huf_x1t_bdefs.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Lemma x1A_open : forall RNG SPV SPA lo DT DTB WK wksz FF, x1A_hyps RNG SPV SPA lo DT DTB WK wksz FF ->
  forall G : Prop, (4096 <= DT ->
    DT + DTB <= 2^47 ->
    DT mod 4 = 0 ->
    4096 <= WK ->
    WK + wksz < 2^47 ->
    WK mod 4 = 0 ->
    1492 <= wksz < 2^32 ->
    KHIGH <= lo ->
    ATOP + 4096 <= lo ->
    lo <= SPV - 5936 ->
    SPV + 16 <= 2^47 ->
    SPV mod 16 = 0 ->
    SPV - 336 <= SPA <= SPV - 320 ->
    SPA mod 32 = 0 ->
    (DT + DTB <= lo \/ SPV <= DT) ->
    (WK + wksz <= lo \/ SPV <= WK) ->
    (DT + DTB <= WK \/ WK + wksz <= DT) ->
    FF mod 64 = 0 ->
    4096 <= FF ->
    FF + 64 <= ATOP ->
    ablk FF (FF + 64) ->
    (DT + DTB <= FF \/ FF + 64 <= DT) ->
    (WK + wksz <= FF \/ FF + 64 <= WK) ->
    ablk DT (DT + DTB) ->
    rng RNG DT DTB ->
    rng RNG (shad DT) (shspan DT DTB) ->
    ablk WK (WK + wksz) ->
    rng RNG WK wksz ->
    rng RNG (shad WK) (shspan WK wksz) ->
    rng RNG FF 64 ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG -> G) -> G.
Proof. intros until FF. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31). eapply K; eassumption. Qed.
Ltac open_hx HY := apply (x1A_open _ _ _ _ _ _ _ _ _ HY); intros DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.

Lemma XB_open : forall m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1,
  XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1 ->
  forall G : Prop, (u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
    zlen dt = DTB ->
    Forall isbyte dt ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
    u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
    zlen rst = 13 ->
    Forall (fun v : Z => 0 <= v) rst ->
    stk bsegs m1 (WK + 104) (WK + 980) ->
    u8arr bsegs m1 (WK + 980) syb ->
    zlen syb = 256 ->
    stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
    wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X1FRB DT WK FF r tl k176 jA jA2 jC jD jB jE) -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & FR). eapply K; eassumption. Qed.
Ltac open_xb I := apply (XB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR; unfold X1FRB in FR.
Lemma XB_close : forall m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1,
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
  zlen dt = DTB ->
  Forall isbyte dt ->
  u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
  u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
  u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
  zlen rst = 13 ->
  Forall (fun v : Z => 0 <= v) rst ->
  stk bsegs m1 (WK + 104) (WK + 980) ->
  u8arr bsegs m1 (WK + 980) syb ->
  zlen syb = 256 ->
  stk bsegs m1 (WK + 1492) (WK + wksz) ->
  stk bsegs m1 lo SPA ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
  wmono bsegs m5 m1 ->
  rw_cells bsegs m1 SPA (X1FRB DT WK FF r tl k176 jA jA2 jC jD jB jE) ->
  XB m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl k176 jA jA2 jC jD jB jE dt rst syb m1.
Proof. intros. unfold XB. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_xb := unfold X1FRB; eapply XB_close; try eassumption.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?u32b_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.
End CANSEC1.

Ltac open_hx HY := apply (x1A_open _ _ _ _ _ _ _ _ _ HY); intros DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.
Ltac open_xb I := apply (XB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RST RSTLEN RSTNN STS SYC SYLEN WKR STK MI MU WM FR; unfold X1FRB in FR.
Ltac close_xb := unfold X1FRB; eapply XB_close; try eassumption.
Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?u32b_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.
Section CANSEC2. Context {rc : runConstT}.
Lemma XF_open : forall m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1,
  XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1 ->
  forall G : Prop, (4 + 2 * 2 ^ tl <= DTB ->
    u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
    zlen dt = DTB ->
    Forall isbyte dt ->
    u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
    u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
    zlen rst = 13 ->
    stk bsegs m1 (WK + 104) (WK + 980) ->
    u8arr bsegs m1 (WK + 980) syb ->
    zlen syb = 256 ->
    stk bsegs m1 (WK + 1492) (WK + wksz) ->
    stk bsegs m1 lo SPA ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
    wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0) ->
    XFR2 SPA WK rsacc sym m1 ->
    rw_cells bsegs m1 (SPA + 160) (X1FR4 DT WK FF j192) -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (HT & H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & HL). eapply K; eassumption. Qed.
Ltac open_xf I := apply (XF_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTF DTC DTLEN DTBY HWC RK RST RSTLEN STS SYC SYLEN WKR STK MI MU WM FR1 F2 FR4; unfold X1FR1 in FR1; unfold X1FR4 in FR4;
  destruct F2 as (k104 & k112 & k120 & k128 & k136 & k144 & k152 & FR2).
Lemma XF_close : forall m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1,
  4 + 2 * 2 ^ tl <= DTB ->
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
  zlen dt = DTB ->
  Forall isbyte dt ->
  u8arr bsegs m1 (WK + 1236) (map (Z_to_bv 8) hw) ->
  u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rank)) ->
  u8arr bsegs m1 (WK + 52) (map (Z_to_bv 8) (u32b rst)) ->
  zlen rst = 13 ->
  stk bsegs m1 (WK + 104) (WK + 980) ->
  u8arr bsegs m1 (WK + 980) syb ->
  zlen syb = 256 ->
  stk bsegs m1 (WK + 1492) (WK + wksz) ->
  stk bsegs m1 lo SPA ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + DTB); (WK, WK + wksz); (SPV - 5440, SPA + 216); (FF + 32, FF + 36)] m5 m1 ->
  wmono bsegs m5 m1 ->
  rw_cells bsegs m1 SPA (X1FR1 DT WK FF r tl j0) ->
  XFR2 SPA WK rsacc sym m1 ->
  rw_cells bsegs m1 (SPA + 160) (X1FR4 DT WK FF j192) ->
  XF m5 SPV SPA lo DT DTB WK wksz FF r hw rank tl j0 j192 dt rst syb rsacc sym m1.
Proof. intros. unfold XF. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_xf := unfold X1FR1, X1FR4; eapply XF_close; try eassumption; try (unfold XFR2; do 7 eexists; eassumption); try eassumption.
End CANSEC2.
Ltac open_xf I := apply (XF_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTF DTC DTLEN DTBY HWC RK RST RSTLEN STS SYC SYLEN WKR STK MI MU WM FR1 F2 FR4; unfold X1FR1 in FR1; unfold X1FR4 in FR4;
  destruct F2 as (k104 & k112 & k120 & k128 & k136 & k144 & k152 & FR2).
Ltac close_xf := unfold X1FR1, X1FR4; eapply XF_close; try eassumption; try (unfold XFR2; do 7 eexists; eassumption); try eassumption.
