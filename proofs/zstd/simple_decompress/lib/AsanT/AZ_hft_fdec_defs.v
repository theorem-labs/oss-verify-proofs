(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufFse ZdSeqTable.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsan KXAutoA.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_hft_iface AZ_hft_initds.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Export AZ_hft_dsym.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Notation FD_WB DST cap SPB := [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] (only parsing).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition fdA_hyps (RNG : footprint) (SPV SPB lo DST cap SRC n WK wksz DT hs tl FF : Z) : Prop :=
  5 <= tl <= 9
  /\ 4096 <= DST
  /\ 0 <= cap
  /\ cap <= 65536
  /\ DST + cap < 2^47
  /\ 4096 <= SRC
  /\ 0 <= n
  /\ n <= 65536
  /\ SRC + n < 2^47
  /\ 1 <= hs
  /\ hs <= n
  /\ 4096 <= WK
  /\ 0 <= wksz
  /\ wksz < 2^32
  /\ WK + wksz < 2^47
  /\ WK mod 4 = 0
  /\ DT = WK + 512
  /\ 516 + 4 * 2^tl <= wksz
  /\ 4096 <= lo
  /\ lo <= SPV - 4992
  /\ SPV + 16 < 2^47
  /\ SPV mod 16 = 0
  /\ KHIGH <= lo
  /\ ATOP + 4096 <= lo
  /\ SPV - 240 <= SPB
  /\ SPB <= SPV - 224
  /\ SPB mod 32 = 0
  /\ (DST + cap <= lo \/ SPV <= DST)
  /\ (WK + wksz <= lo \/ SPV <= WK)
  /\ (SRC + n <= lo \/ SPV <= SRC)
  /\ (DST + cap <= WK \/ WK + wksz <= DST)
  /\ (DST + cap <= SRC \/ SRC + n <= DST)
  /\ (WK + wksz <= SRC \/ SRC + n <= WK)
  /\ FF mod 64 = 0
  /\ ablk FF (FF + 64)
  /\ FF + 64 <= ATOP
  /\ rng RNG FF 64
  /\ rng RNG (shad FF) 8
  /\ (DST + cap <= FF \/ FF + 64 <= DST)
  /\ (WK + wksz <= FF \/ FF + 64 <= WK)
  /\ (n = 0 \/ SRC + n <= FF \/ FF + 64 <= SRC)
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG
  /\ (0 < cap -> rng RNG DST cap)
  /\ (0 < cap -> rng RNG (shad DST) (shspan DST cap))
  /\ (AIMG_HI <= DST /\ DST + cap <= ATOP /\ (DST + cap <= KLS \/ KHIGH <= DST))
  /\ rng RNG SRC n
  /\ rng RNG (shad SRC) (shspan SRC n)
  /\ ablk SRC (SRC + n)
  /\ rng RNG WK wksz
  /\ rng RNG (shad WK) (shspan WK wksz)
  /\ ablk WK (WK + wksz)
  /\ rng RNG (shad SPB) 20.

Lemma fdA_open : forall RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF, fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF ->
  forall G : Prop, (5 <= tl <= 9 ->
    4096 <= DST ->
    0 <= cap ->
    cap <= 65536 ->
    DST + cap < 2^47 ->
    4096 <= SRC ->
    0 <= n ->
    n <= 65536 ->
    SRC + n < 2^47 ->
    1 <= hs ->
    hs <= n ->
    4096 <= WK ->
    0 <= wksz ->
    wksz < 2^32 ->
    WK + wksz < 2^47 ->
    WK mod 4 = 0 ->
    DT = WK + 512 ->
    516 + 4 * 2^tl <= wksz ->
    4096 <= lo ->
    lo <= SPV - 4992 ->
    SPV + 16 < 2^47 ->
    SPV mod 16 = 0 ->
    KHIGH <= lo ->
    ATOP + 4096 <= lo ->
    SPV - 240 <= SPB ->
    SPB <= SPV - 224 ->
    SPB mod 32 = 0 ->
    (DST + cap <= lo \/ SPV <= DST) ->
    (WK + wksz <= lo \/ SPV <= WK) ->
    (SRC + n <= lo \/ SPV <= SRC) ->
    (DST + cap <= WK \/ WK + wksz <= DST) ->
    (DST + cap <= SRC \/ SRC + n <= DST) ->
    (WK + wksz <= SRC \/ SRC + n <= WK) ->
    FF mod 64 = 0 ->
    ablk FF (FF + 64) ->
    FF + 64 <= ATOP ->
    rng RNG FF 64 ->
    rng RNG (shad FF) 8 ->
    (DST + cap <= FF \/ FF + 64 <= DST) ->
    (WK + wksz <= FF \/ FF + 64 <= WK) ->
    (n = 0 \/ SRC + n <= FF \/ FF + 64 <= SRC) ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG ->
    (0 < cap -> rng RNG DST cap) ->
    (0 < cap -> rng RNG (shad DST) (shspan DST cap)) ->
    (AIMG_HI <= DST /\ DST + cap <= ATOP /\ (DST + cap <= KLS \/ KHIGH <= DST)) ->
    rng RNG SRC n ->
    rng RNG (shad SRC) (shspan SRC n) ->
    ablk SRC (SRC + n) ->
    rng RNG WK wksz ->
    rng RNG (shad WK) (shspan WK wksz) ->
    ablk WK (WK + wksz) ->
    rng RNG (shad SPB) 20 -> G) -> G.
Proof. intros until FF. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31 & Y32 & Y33 & Y34 & Y35 & Y36 & Y37 & Y38 & Y39 & Y40 & Y41 & Y42 & Y43 & Y44 & Y45 & Y46 & Y47 & Y48 & Y49 & Y50 & Y51 & Y52). eapply K; eassumption. Qed.
Ltac open_hy HY := apply (fdA_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY); intros TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH WKA DTE ROOM LO0 LOS SPR SPA KLO BOT SPB0 SPB1 SPBA OFFDST OFFWK OFFSRC DSTWK DSTSRC WKSRC F64 FFH FFT RFF RSFF FFDST FFWK FFSRC RSTK RI RDST RSDST ABD RSRC RSSRC ABS RWK RSWK ABW RSFR.
Lemma fdA_close : forall RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF,
  5 <= tl <= 9 ->
  4096 <= DST ->
  0 <= cap ->
  cap <= 65536 ->
  DST + cap < 2^47 ->
  4096 <= SRC ->
  0 <= n ->
  n <= 65536 ->
  SRC + n < 2^47 ->
  1 <= hs ->
  hs <= n ->
  4096 <= WK ->
  0 <= wksz ->
  wksz < 2^32 ->
  WK + wksz < 2^47 ->
  WK mod 4 = 0 ->
  DT = WK + 512 ->
  516 + 4 * 2^tl <= wksz ->
  4096 <= lo ->
  lo <= SPV - 4992 ->
  SPV + 16 < 2^47 ->
  SPV mod 16 = 0 ->
  KHIGH <= lo ->
  ATOP + 4096 <= lo ->
  SPV - 240 <= SPB ->
  SPB <= SPV - 224 ->
  SPB mod 32 = 0 ->
  (DST + cap <= lo \/ SPV <= DST) ->
  (WK + wksz <= lo \/ SPV <= WK) ->
  (SRC + n <= lo \/ SPV <= SRC) ->
  (DST + cap <= WK \/ WK + wksz <= DST) ->
  (DST + cap <= SRC \/ SRC + n <= DST) ->
  (WK + wksz <= SRC \/ SRC + n <= WK) ->
  FF mod 64 = 0 ->
  ablk FF (FF + 64) ->
  FF + 64 <= ATOP ->
  rng RNG FF 64 ->
  rng RNG (shad FF) 8 ->
  (DST + cap <= FF \/ FF + 64 <= DST) ->
  (WK + wksz <= FF \/ FF + 64 <= WK) ->
  (n = 0 \/ SRC + n <= FF \/ FF + 64 <= SRC) ->
  rng RNG lo (SPV - lo) ->
  rng_aimg RNG ->
  (0 < cap -> rng RNG DST cap) ->
  (0 < cap -> rng RNG (shad DST) (shspan DST cap)) ->
  (AIMG_HI <= DST /\ DST + cap <= ATOP /\ (DST + cap <= KLS \/ KHIGH <= DST)) ->
  rng RNG SRC n ->
  rng RNG (shad SRC) (shspan SRC n) ->
  ablk SRC (SRC + n) ->
  rng RNG WK wksz ->
  rng RNG (shad WK) (shspan WK wksz) ->
  ablk WK (WK + wksz) ->
  rng RNG (shad SPB) 20 ->
  fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
Proof. intros. unfold fdA_hyps. repeat (split; [eassumption|]). eassumption. Qed.

(* [comment removed for export] *)
Definition fdA_an (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte) : Prop :=
  unpoisoned mA DST (DST + cap)
  /\ unpoisoned mA SRC (SRC + n)
  /\ unpoisoned mA WK (WK + wksz)
  /\ azstk RNG mA lo SPV
  /\ art mA
  /\ aro_client RNG mA
  /\ rw_cells bsegs mA DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)]
  /\ u8arr bsegs mA (DT + 4) (map (Z_to_bv 8) tb)
  /\ fd_tblv tl fast tb
  /\ stk bsegs mA (DT + 4 + 4 * 2^tl) (WK + wksz)
  /\ stk bsegs mA WK DT
  /\ bytes_at bsegs mA SRC src
  /\ zlen src = n
  /\ rw_cells bsegs mA (SPB + 8) [C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 FF)]
  /\ rw_cells bsegs mA (SPB + 40) [C8 (Z_to_bv 64 FF)]
  /\ stk bsegs mA SPB (SPB + 8)
  /\ stk bsegs mA (SPB + 32) (SPB + 40)
  /\ stk bsegs mA (SPB + 120) (SPV + -104)
  /\ mem_inv bsegs mA.

Lemma fdA_an_open : forall RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src, fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src ->
  forall G : Prop, (unpoisoned mA DST (DST + cap) ->
    unpoisoned mA SRC (SRC + n) ->
    unpoisoned mA WK (WK + wksz) ->
    azstk RNG mA lo SPV ->
    art mA ->
    aro_client RNG mA ->
    rw_cells bsegs mA DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)] ->
    u8arr bsegs mA (DT + 4) (map (Z_to_bv 8) tb) ->
    fd_tblv tl fast tb ->
    stk bsegs mA (DT + 4 + 4 * 2^tl) (WK + wksz) ->
    stk bsegs mA WK DT ->
    bytes_at bsegs mA SRC src ->
    zlen src = n ->
    rw_cells bsegs mA (SPB + 8) [C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 FF)] ->
    rw_cells bsegs mA (SPB + 40) [C8 (Z_to_bv 64 FF)] ->
    stk bsegs mA SPB (SPB + 8) ->
    stk bsegs mA (SPB + 32) (SPB + 40) ->
    stk bsegs mA (SPB + 120) (SPV + -104) ->
    mem_inv bsegs mA -> G) -> G.
Proof. intros until src. intros AN G K. destruct AN as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18). eapply K; eassumption. Qed.
Ltac open_an AN := apply (fdA_an_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AN); intros UDj USj UWj AZj ARTj ACj DTHj TBj TBV WSj WKLOj SRCBj SRCLEN FAj FBj SK0j SK1j SK2j MIj.
Lemma fdA_an_close : forall RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src,
  unpoisoned mA DST (DST + cap) ->
  unpoisoned mA SRC (SRC + n) ->
  unpoisoned mA WK (WK + wksz) ->
  azstk RNG mA lo SPV ->
  art mA ->
  aro_client RNG mA ->
  rw_cells bsegs mA DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)] ->
  u8arr bsegs mA (DT + 4) (map (Z_to_bv 8) tb) ->
  fd_tblv tl fast tb ->
  stk bsegs mA (DT + 4 + 4 * 2^tl) (WK + wksz) ->
  stk bsegs mA WK DT ->
  bytes_at bsegs mA SRC src ->
  zlen src = n ->
  rw_cells bsegs mA (SPB + 8) [C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 FF)] ->
  rw_cells bsegs mA (SPB + 40) [C8 (Z_to_bv 64 FF)] ->
  stk bsegs mA SPB (SPB + 8) ->
  stk bsegs mA (SPB + 32) (SPB + 40) ->
  stk bsegs mA (SPB + 120) (SPV + -104) ->
  mem_inv bsegs mA ->
  fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.
Proof. intros. unfold fdA_an. repeat (split; [eassumption|]). eassumption. Qed.

(* [comment removed for export] *)
Definition FDM (mA : amem) (SPV SPB lo DST cap SRC hs DT : Z) (st1 st2 : Z) (cont : word) (bc ptr : Z) (pad : list byte) (mx : amem) : Prop :=
  rw_cells bsegs mx (SPB + 48) [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells bsegs mx (SPB + 64) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells bsegs mx (SPB + 80) (bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs))
  /\ stk bsegs mx DST (DST + cap)
  /\ stk bsegs mx lo SPB
  /\ mem_inv bsegs mx
  /\ munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mx
  /\ wmono bsegs mA mx.

Lemma FDM_open : forall mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx,
  FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx ->
  forall G : Prop, (rw_cells bsegs mx (SPB + 48) [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs mx (SPB + 64) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs mx (SPB + 80) (bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs)) ->
    stk bsegs mx DST (DST + cap) ->
    stk bsegs mx lo SPB ->
    mem_inv bsegs mx ->
    munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mx ->
    wmono bsegs mA mx -> G) -> G.
Proof. intros until mx. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). eapply K; eassumption. Qed.
Ltac open_fdm I := apply (FDM_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros S2 S1 BDC STD STL MI MU WM; unfold bitd_cells in BDC.
Lemma FDM_close : forall mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx,
  rw_cells bsegs mx (SPB + 48) [C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells bsegs mx (SPB + 64) [C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells bsegs mx (SPB + 80) (bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs)) ->
  stk bsegs mx DST (DST + cap) ->
  stk bsegs mx lo SPB ->
  mem_inv bsegs mx ->
  munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mx ->
  wmono bsegs mA mx ->
  FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx.
Proof. intros. unfold FDM. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_fdm := unfold bitd_cells; eapply FDM_close; unfold bitd_cells; eassumption.

Definition FDMS (mA : amem) (SPV SPB lo DST cap SRC hs DT : Z) (j48 j64 j80 j88 j92 j96 : list byte) (mx : amem) : Prop :=
  rw_cells bsegs mx (SPB + 48) [CB 8 j48; C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells bsegs mx (SPB + 64) [CB 8 j64; C8 (Z_to_bv 64 (DT + 4))]
  /\ rw_cells bsegs mx (SPB + 80) [CB 8 j80; CB 4 j88; CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))]
  /\ stk bsegs mx DST (DST + cap)
  /\ stk bsegs mx lo SPB
  /\ mem_inv bsegs mx
  /\ munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mx
  /\ wmono bsegs mA mx.

Lemma FDMS_open : forall mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx,
  FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx ->
  forall G : Prop, (rw_cells bsegs mx (SPB + 48) [CB 8 j48; C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs mx (SPB + 64) [CB 8 j64; C8 (Z_to_bv 64 (DT + 4))] ->
    rw_cells bsegs mx (SPB + 80) [CB 8 j80; CB 4 j88; CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] ->
    stk bsegs mx DST (DST + cap) ->
    stk bsegs mx lo SPB ->
    mem_inv bsegs mx ->
    munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mx ->
    wmono bsegs mA mx -> G) -> G.
Proof. intros until mx. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7). eapply K; eassumption. Qed.
Ltac open_fdms I := apply (FDMS_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros S2 S1 BDC STD STL MI MU WM.
Lemma FDMS_close : forall mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx,
  rw_cells bsegs mx (SPB + 48) [CB 8 j48; C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells bsegs mx (SPB + 64) [CB 8 j64; C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells bsegs mx (SPB + 80) [CB 8 j80; CB 4 j88; CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] ->
  stk bsegs mx DST (DST + cap) ->
  stk bsegs mx lo SPB ->
  mem_inv bsegs mx ->
  munch [(DST, DST + cap); (SPB - 2224, SPB); (SPB + 48, SPB + 120)] mA mx ->
  wmono bsegs mA mx ->
  FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx.
Proof. intros. unfold FDMS. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_fdms := eapply FDMS_close; eassumption.

Lemma fdm_to_fdms : forall mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx,
  FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx ->
  exists j48 j64 j80 j88 j92 j96, FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx.
Proof.
  intros until mx. intros FD. destruct FD as (S2 & S1 & BDC & STD & STL & MI & MU & WM). unfold bitd_cells in BDC.
  pose proof (rw_cells_merge bsegs mx (SPB + 48) [] [C8 (Z_to_bv 64 st2)] [C8 (Z_to_bv 64 (DT + 4))] S2) as X2.
  pose proof (rw_cells_merge bsegs mx (SPB + 64) [] [C8 (Z_to_bv 64 st1)] [C8 (Z_to_bv 64 (DT + 4))] S1) as X1.
  pose proof (rw_cells_merge bsegs mx (SPB + 80) [] [C8 cont]
    [C4 (Z_to_bv 64 bc); CB 4 pad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] BDC) as B1.
  pose proof (rw_cells_merge bsegs mx (SPB + 80) [CB (cells_size [C8 cont]) (cells_bytes [C8 cont])] [C4 (Z_to_bv 64 bc)]
    [CB 4 pad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] B1) as B2.
  pose proof (rw_cells_merge bsegs mx (SPB + 80)
    [CB (cells_size [C8 cont]) (cells_bytes [C8 cont]); CB (cells_size [C4 (Z_to_bv 64 bc)]) (cells_bytes [C4 (Z_to_bv 64 bc)]); CB 4 pad]
    [C8 (Z_to_bv 64 ptr)] [C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] B2) as B3.
  cbn [app cells_size csize Nat.add] in X2, X1, B3.
  do 6 eexists. unfold FDMS. split; [exact X2|]. split; [exact X1|]. split; [exact B3|].
  repeat (split; [eassumption|]). exact WM.
Qed.

Lemma fd_cb4_as_c4 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 4 j :: post) -> exists w, rw_cells segs m A (pre ++ C4 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common.WStr.le4_of_bytes by exact WFJ. reflexivity.
Qed.

Lemma fdms_to_fdm : forall mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx,
  FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx ->
  exists st1 st2 cont bc ptr, FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr j92 mx.
Proof.
  intros until mx. intros FD. destruct FD as (S2 & S1 & BDC & STD & STL & MI & MU & WM).
  destruct (cb8_as_c8 bsegs mx (SPB + 48) [] j48 [C8 (Z_to_bv 64 (DT + 4))] S2) as [w2 X2].
  destruct (cb8_as_c8 bsegs mx (SPB + 64) [] j64 [C8 (Z_to_bv 64 (DT + 4))] S1) as [w1 X1].
  destruct (cb8_as_c8 bsegs mx (SPB + 80) [] j80
    [CB 4 j88; CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] BDC) as [wc B1].
  destruct (fd_cb4_as_c4 bsegs mx (SPB + 80) [C8 wc] j88
    [CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] B1) as [wb B2].
  destruct (cb8_as_c8 bsegs mx (SPB + 80) [C8 wc; C4 wb; CB 4 j92] j96
    [C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))] B2) as [wp B3].
  cbn [app] in X2, X1, B3.
  exists (bv_unsigned w1), (bv_unsigned w2), wc, (bv_unsigned wb), (bv_unsigned wp).
  unfold FDM, bitd_cells. rewrite !Z_to_bv_bv_unsigned.
  split; [exact X2|]. split; [exact X1|]. split; [exact B3|].
  repeat (split; [eassumption|]). exact WM.
Qed.

(* [comment removed for export] *)
Definition EXB (mA : amem) (SPV SPB lo DST cap : Z) (mx : amem) : Prop :=
  munch (FD_WB DST cap SPB) mA mx /\ wmono bsegs mA mx /\ mem_inv bsegs mx /\ stk bsegs mx lo SPB /\ stk bsegs mx DST (DST + cap)
  /\ (exists cs, rw_cells bsegs mx (SPB + 48) cs /\ cells_size cs = 72%nat).
Lemma exb_of_fdm : forall mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx,
  FDM mA SPV SPB lo DST cap SRC hs DT st1 st2 cont bc ptr pad mx -> EXB mA SPV SPB lo DST cap mx.
Proof.
  intros until mx. intros FD. destruct FD as (S2 & S1 & BDC & STD & STL & MI & MU & WM). unfold EXB.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STL|]. split; [exact STD|].
  assert (C1 : rw_cells bsegs mx (SPB + 64) ([C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))] ++ bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs))).
  { apply (proj2 (rw_cells_app bsegs mx (SPB + 64) _ _)). split; [exact S1|]. cbn [cells_size csize Nat.add]. replace (SPB + 64 + Z.of_nat 16) with (SPB + 80) by lia. exact BDC. }
  assert (C2 : rw_cells bsegs mx (SPB + 48) ([C8 (Z_to_bv 64 st2); C8 (Z_to_bv 64 (DT + 4))] ++ ([C8 (Z_to_bv 64 st1); C8 (Z_to_bv 64 (DT + 4))] ++ bitd_cells cont (Z_to_bv 64 bc) pad ptr (SRC + hs)))).
  { apply (proj2 (rw_cells_app bsegs mx (SPB + 48) _ _)). split; [exact S2|]. cbn [cells_size csize Nat.add]. replace (SPB + 48 + Z.of_nat 16) with (SPB + 64) by lia. exact C1. }
  eexists. split; [exact C2|]. reflexivity.
Qed.
Lemma exb_of_fdms : forall mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx,
  FDMS mA SPV SPB lo DST cap SRC hs DT j48 j64 j80 j88 j92 j96 mx -> EXB mA SPV SPB lo DST cap mx.
Proof.
  intros until mx. intros FD. destruct FD as (S2 & S1 & BDC & STD & STL & MI & MU & WM). unfold EXB.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STL|]. split; [exact STD|].
  assert (C1 : rw_cells bsegs mx (SPB + 64) ([CB 8 j64; C8 (Z_to_bv 64 (DT + 4))] ++
    [CB 8 j80; CB 4 j88; CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))])).
  { apply (proj2 (rw_cells_app bsegs mx (SPB + 64) _ _)). split; [exact S1|]. cbn [cells_size csize Nat.add]. replace (SPB + 64 + Z.of_nat 16) with (SPB + 80) by lia. exact BDC. }
  assert (C2 : rw_cells bsegs mx (SPB + 48) ([CB 8 j48; C8 (Z_to_bv 64 (DT + 4))] ++ ([CB 8 j64; C8 (Z_to_bv 64 (DT + 4))] ++
    [CB 8 j80; CB 4 j88; CB 4 j92; CB 8 j96; C8 (Z_to_bv 64 (SRC + hs)); C8 (Z_to_bv 64 (SRC + hs + 8))]))).
  { apply (proj2 (rw_cells_app bsegs mx (SPB + 48) _ _)). split; [exact S2|]. cbn [cells_size csize Nat.add]. replace (SPB + 48 + Z.of_nat 16) with (SPB + 64) by lia. exact C1. }
  eexists. split; [exact C2|]. reflexivity.
Qed.
(* [comment removed for export] *)
Definition fd_exitK {rc : runConstT} (Q : machine_state -> Prop) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mA : amem) (SPV SPB lo DST cap FF : Z) : Prop :=
  forall mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x17 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EXB mA SPV SPB lo DST cap mx -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 x17
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0xac208) fc None mx (seg_rom bsegs)).

Definition fd_exitKc {rc : runConstT} (Q : machine_state -> Prop) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mA : amem) (SPV SPB lo DST cap FF : Z) : Prop :=
  forall mx r (x1 x2 x5 x6 x7 x10 x11 x12 x13 x14 x16 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    EXB mA SPV SPB lo DST cap mx -> 0 <= r < 2^64 -> (zd_is_error r = true \/ r <= cap) ->
    Q (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB) x10 x11 x12 x13 x14 (Z_to_bv 64 r) x16 (Z_to_bv 64 FF)
             (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0xac20c) fc None mx (seg_rom bsegs)).

(* [comment removed for export] *)
Lemma fd_disjoint_from_above : forall W A n K, Forall (fun iv : Z * Z => K <= fst iv) W -> A + n <= K -> disjoint_from W A n.
Proof.
  induction W as [|[lo' hi'] W IH]; intros A n K HW HA; cbn; [exact I|].
  inversion HW; subst. cbn in *. split; [lia|]. eapply IH; eassumption.
Qed.
Lemma fd_art_transport : forall W m m', art m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv : Z * Z => 0xd1740 <= fst iv) W -> art m'.
Proof.
  intros W m m' (GOT & RIC & SHB & INI & LAY & REAL) MU WM HW.
  unfold art. repeat split.
  all: first [ eapply rw_cells_transport; [eassumption| exact MU| exact WM| eapply fd_disjoint_from_above; [exact HW| cbn; lia]]
             | eapply ro_cells_transport; [eassumption| exact MU| eapply fd_disjoint_from_above; [exact HW| cbn; lia]] ].
Qed.

Section G.
  Variables (RNG : footprint) (mA : amem) (SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF : Z) (tb : list Z) (src : list byte).
  Hypothesis HY : fdA_hyps RNG SPV SPB lo DST cap SRC n WK wksz DT hs tl FF.
  Hypothesis AN : fdA_an RNG mA SPV SPB lo DST cap SRC n WK wksz DT hs tl fast FF tb src.

  Lemma fd_bands : KHIGH + 4992 <= SPV /\ SPV + 16 <= KEND /\ (WK + wksz <= KLS \/ KHIGH <= WK) /\ (SRC + n <= KLS \/ KHIGH <= SRC)
                   /\ AIMG_HI <= WK /\ AIMG_HI <= SRC /\ AIMG_HI <= FF /\ 32 <= 2^tl <= 512.
  Proof.
    open_hy HY. pose proof (ablk_lin _ _ ABW) as (W1 & _). pose proof (ablk_lin _ _ ABS) as (S1 & _). pose proof (ablk_lin _ _ FFH) as (F1 & _).
    assert (P2 : 32 <= 2^tl <= 512) by (split; [change 32 with (2^5) | change 512 with (2^9)]; apply Z.pow_le_mono_r; clear - TLR; lia).
    unfold ablk in ABW, ABS. unfold KHIGH, KLS, AIMG_HI, KEND in *.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. destruct RSTK as [_ RS2]. clear - KLO LOS BOT ABW ABS W1 S1 F1 P2 ATR SPR. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fd_seps : (DST + cap <= SPB \/ SPB + 120 <= DST) /\ (DST + cap <= DT + 4 \/ DT + 4 + 4 * 2^tl <= DST) /\ (DST + cap <= SRC \/ SRC + n <= DST)
                  /\ (SPB + 48 + 72 <= SRC \/ SRC + n <= SPB + 48) /\ (SPB + 48 + 72 <= DT + 4 \/ DT + 4 + 4 * 2^tl <= SPB + 48)
                  /\ (SPB + 120 <= SRC \/ SRC + n <= SPB - 2224) /\ (SPB + 120 <= WK \/ WK + wksz <= SPB - 2224).
  Proof.
    open_hy HY. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2).
    clear - OFFDST OFFWK OFFSRC DSTWK DSTSRC SPB0 SPB1 LOS DTE ROOM P2 CAP0 N0. repeat split; lia.
  Qed.

  Lemma fd_aappW : aappW (FD_WB DST cap SPB).
  Proof.
    open_hy HY. pose proof fd_bands as (B1 & _). destruct ABD as (_ & _ & AB3). unfold aappW. unfold KLS, KLOW, KHIGH in *.
    clear - B1 AB3 SPB0 SPB1. repeat (constructor; [cbn [fst snd]; lia|]). constructor.
  Qed.

  (* [comment removed for export] *)
  Lemma fd_unp_M : forall mx X Y, unpoisoned mA X Y -> munch (FD_WB DST cap SPB) mA mx -> 0 <= X -> X < Y -> Y <= KEND -> unpoisoned mx X Y.
  Proof.
    intros mx X Y U MU X0 XY YK. eapply unpoisoned_munch; [exact U | exact MU |].
    apply aappW_shadow_disjoint; [exact fd_aappW | | | |]; rewrite ?shad_div; unfold ASHOFF, KEND in *; clear - X0 XY YK; Z.div_mod_to_equations; lia.
  Qed.
  Lemma fd_udM : forall mx, munch (FD_WB DST cap SPB) mA mx -> unpoisoned mx DST (DST + cap).
  Proof.
    intros mx MU. open_hy HY. open_an AN. destruct (Z.eq_dec cap 0) as [E|NE].
    - destruct UDj as (U1 & U2 & _). split; [exact U1|]. split; [exact U2|]. intros G HG. exfalso. clear - HG E. lia.
    - eapply fd_unp_M; [exact UDj | exact MU | | |]; unfold KEND; clear - NE CAP0 DSTL DSTH; lia.
  Qed.
  Lemma fd_usM : forall mx, munch (FD_WB DST cap SPB) mA mx -> unpoisoned mx SRC (SRC + n).
  Proof. intros mx MU. open_hy HY. open_an AN. eapply fd_unp_M; [exact USj | exact MU | | |]; unfold KEND; clear - HS1 HSN SRCL SRCH; lia. Qed.
  Lemma fd_uwM : forall mx, munch (FD_WB DST cap SPB) mA mx -> unpoisoned mx WK (WK + wksz).
  Proof. intros mx MU. open_hy HY. open_an AN. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2). eapply fd_unp_M; [exact UWj | exact MU | | |]; unfold KEND; clear - ROOM WKL WKH P2; lia. Qed.
  Lemma fd_azM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> azstk RNG mx lo SPV.
  Proof. intros mx MU WM. open_hy HY. open_an AN. eapply azstk_transport; [exact AZj | exact MU | exact WM | exact fd_aappW | clear - LOS; lia]. Qed.
  Lemma fd_acM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> aro_client RNG mx.
  Proof. intros mx MU WM. open_an AN. eapply aro_client_transport; [exact ACj | exact MU | exact WM | exact fd_aappW]. Qed.
  Lemma fd_artM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> art mx.
  Proof.
    intros mx MU WM. open_hy HY. open_an AN. pose proof fd_bands as (B1 & _). destruct ABD as (AB1 & _ & _). unfold AIMG_HI, KHIGH in *.
    eapply fd_art_transport; [exact ARTj| exact MU| exact WM|]. clear - B1 AB1 SPB0. repeat (constructor; [cbn [fst snd]; lia|]). constructor.
  Qed.
  (* [comment removed for export] *)
  Lemma fd_WK_disj : forall X k, WK <= X -> 0 <= k -> X + k <= WK + wksz -> disjoint_from (FD_WB DST cap SPB) X k.
  Proof. intros X k H0 H1 H2. open_hy HY. cbn [disjoint_from]. clear - H0 H1 H2 DSTWK OFFWK SPB0 SPB1 LOS. repeat split; lia. Qed.
  Lemma fd_dthM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> rw_cells bsegs mx DT [C2 (Z_to_bv 64 tl); C2 (Z_to_bv 64 fast)].
  Proof. intros mx MU WM. open_hy HY. open_an AN. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2). eapply rw_cells_transport; [exact DTHj | exact MU | exact WM | apply fd_WK_disj; cbn; clear - DTE ROOM P2; lia]. Qed.
  Lemma fd_tbM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> u8arr bsegs mx (DT + 4) (map (Z_to_bv 8) tb).
  Proof.
    intros mx MU WM. open_hy HY. open_an AN. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2). destruct TBV as (TL & _).
    eapply u8arr_transport; [exact TBj | exact MU | exact WM | apply fd_WK_disj; rewrite ?length_map; clear - DTE ROOM P2 TL; lia].
  Qed.
  Lemma fd_wsM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> stk bsegs mx (DT + 4 + 4 * 2^tl) (WK + wksz).
  Proof. intros mx MU WM. open_hy HY. open_an AN. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2). eapply stk_transport_disjoint; [exact WSj | exact MU | exact WM | apply fd_WK_disj; clear - DTE ROOM P2; lia]. Qed.
  Lemma fd_wkloM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> stk bsegs mx WK DT.
  Proof. intros mx MU WM. open_hy HY. open_an AN. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2). eapply stk_transport_disjoint; [exact WKLOj | exact MU | exact WM | apply fd_WK_disj; clear - DTE ROOM P2; lia]. Qed.
  Lemma fd_srcM : forall mx, munch (FD_WB DST cap SPB) mA mx -> bytes_at bsegs mx SRC src.
  Proof.
    intros mx MU. open_hy HY. open_an AN. eapply bytes_at_transport; [exact SRCBj | exact MU |].
    cbn [disjoint_from]. clear - SRCLEN DSTSRC OFFSRC SPB0 SPB1 LOS N0. repeat split; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fd_faM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx ->
    rw_cells bsegs mx (SPB + 8) [C8 (Z_to_bv 64 DST); C8 (Z_to_bv 64 0x7fff8000); C8 (Z_to_bv 64 FF)].
  Proof. intros mx MU WM. open_hy HY. open_an AN. eapply rw_cells_transport; [exact FAj | exact MU | exact WM | cbn; clear - OFFDST SPB0 SPB1 LOS CAP0; repeat split; lia]. Qed.
  Lemma fd_fbM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> rw_cells bsegs mx (SPB + 40) [C8 (Z_to_bv 64 FF)].
  Proof. intros mx MU WM. open_hy HY. open_an AN. eapply rw_cells_transport; [exact FBj | exact MU | exact WM | cbn; clear - OFFDST SPB0 SPB1 LOS CAP0; repeat split; lia]. Qed.
  Lemma fd_sk0M : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> stk bsegs mx SPB (SPB + 8).
  Proof. intros mx MU WM. open_hy HY. open_an AN. eapply stk_transport_disjoint; [exact SK0j | exact MU | exact WM | cbn; clear - OFFDST SPB0 SPB1 LOS CAP0; repeat split; lia]. Qed.
  Lemma fd_sk1M : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> stk bsegs mx (SPB + 32) (SPB + 40).
  Proof. intros mx MU WM. open_hy HY. open_an AN. eapply stk_transport_disjoint; [exact SK1j | exact MU | exact WM | cbn; clear - OFFDST SPB0 SPB1 LOS CAP0; repeat split; lia]. Qed.
  Lemma fd_sk2M : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> stk bsegs mx (SPB + 120) (SPV + -104).
  Proof. intros mx MU WM. open_hy HY. open_an AN. eapply stk_transport_disjoint; [exact SK2j | exact MU | exact WM | cbn; clear - OFFDST SPB0 SPB1 LOS CAP0; repeat split; lia]. Qed.

  (* [comment removed for export] *)
  Lemma fd_astk : astk RNG lo SPB.
  Proof. open_hy HY. split; [exact KLO|]. split; [eapply rng_sub; [exact RSTK| clear; lia| clear - SPB1; lia] | exact RI]. Qed.
  Lemma fd_aro_frameM : forall mx X k, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> SPB <= X -> 0 <= k -> X + k <= SPB + 160 -> aro RNG mx X k.
  Proof.
    intros mx X k MU WM H0 H1 H2. open_hy HY. eapply azstk_aro; [exact (fd_azM mx MU WM) | clear - H0 SPB0 LOS; lia | exact H1 | clear - H2 SPB1; lia |].
    eapply rng_sub; [exact RSTK | clear - H0 SPB0 LOS; lia | clear - H2 SPB1; lia].
  Qed.
  Lemma fd_app_frameM : forall mx X k, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> SPB <= X -> 0 <= k -> X + k <= SPB + 160 -> app_blk X (X + k).
  Proof. intros mx X k MU WM H0 H1 H2. open_hy HY. eapply azstk_app; [exact (fd_azM mx MU WM) | clear - H0 SPB0 LOS; lia | exact H1 | clear - H2 SPB1; lia]. Qed.
  Lemma fd_ahull_frameM : forall mx X k, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> SPB <= X -> 0 <= k -> X + k <= SPB + 160 -> ahull RNG mx X k.
  Proof. intros mx X k MU WM H0 H1 H2. open_hy HY. eapply azstk_ahull; [exact (fd_azM mx MU WM) | clear - H0 SPB0 LOS; lia | exact H1 | clear - H2 SPB1; lia]. Qed.
  Lemma fd_aro_dtM : forall mx, munch (FD_WB DST cap SPB) mA mx -> aro RNG mx DT 4.
  Proof.
    intros mx MU. open_hy HY. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2).
    split; [eapply unpoisoned_sub; [exact (fd_uwM mx MU) | clear - DTE; lia | clear - DTE ROOM P2; lia]|].
    split; [eapply rng_sub; [exact RWK | clear - DTE; lia | clear - DTE ROOM P2; lia]|].
    destruct (shspan_sub WK wksz DT 4 ltac:(clear - DTE; lia) ltac:(clear; lia) ltac:(clear - DTE ROOM P2; lia)) as [S1 S2].
    eapply rng_sub; [exact RSWK | exact S1 | exact S2].
  Qed.
  Lemma fd_aro_tbM : forall mx, munch (FD_WB DST cap SPB) mA mx -> aro RNG mx (DT + 4) (4 * 2^tl).
  Proof.
    intros mx MU. open_hy HY. pose proof fd_bands as (_ & _ & _ & _ & _ & _ & _ & P2).
    split; [eapply unpoisoned_sub; [exact (fd_uwM mx MU) | clear - DTE; lia | clear - DTE ROOM P2; lia]|].
    split; [eapply rng_sub; [exact RWK | clear - DTE; lia | clear - DTE ROOM P2; lia]|].
    destruct (shspan_sub WK wksz (DT + 4) (4 * 2^tl) ltac:(clear - DTE; lia) ltac:(clear - P2; lia) ltac:(clear - DTE ROOM P2; lia)) as [S1 S2].
    eapply rng_sub; [exact RSWK | exact S1 | exact S2].
  Qed.
  Lemma fd_aro_srcM : forall mx, munch (FD_WB DST cap SPB) mA mx -> aro RNG mx (SRC + hs) (n - hs).
  Proof.
    intros mx MU. open_hy HY.
    split; [eapply unpoisoned_sub; [exact (fd_usM mx MU) | clear - HS1; lia | clear - HSN; lia]|].
    split; [eapply rng_sub; [exact RSRC | clear - HS1; lia | clear - HSN; lia]|].
    destruct (shspan_sub SRC n (SRC + hs) (n - hs) ltac:(clear - HS1; lia) ltac:(clear - HSN; lia) ltac:(clear - HSN; lia)) as [S1 S2].
    eapply rng_sub; [exact RSSRC | exact S1 | exact S2].
  Qed.
  Lemma fd_src0M : forall mx, munch (FD_WB DST cap SPB) mA mx ->
    bytes_at bsegs mx (SRC + hs) (skipn (Z.to_nat hs) src) /\ zlen (skipn (Z.to_nat hs) src) = n - hs.
  Proof.
    intros mx MU. open_hy HY. pose proof (fd_srcM mx MU) as B. open_an AN. pose proof SRCLEN as L.
    rewrite <- (firstn_skipn (Z.to_nat hs) src) in B. apply bytes_at_app in B. destruct B as [_ B].
    rewrite length_firstn in B. replace (SRC + Z.of_nat (Nat.min (Z.to_nat hs) (length src))) with (SRC + hs) in B by (clear - L HS1 HSN; lia).
    split; [exact B|]. rewrite length_skipn. clear - L HS1 HSN. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma fd_cellA : forall st, 0 <= st < 2^tl ->
    fast <= fc_nb tb st <= tl /\ 0 <= fc_nx tb st /\ fc_nx tb st + 2^(fc_nb tb st) <= 2^tl /\ 0 <= fc_sy tb st < 256
    /\ 0 <= Znth (4 * st) tb < 256 /\ 0 <= Znth (4 * st + 1) tb < 256 /\ 4 * st + 4 <= zlen tb.
  Proof.
    intros st HS. open_hy HY. open_an AN. pose proof TBV as (TL & FR & _ & _).
    destruct (fd_cell tl fast tb st TBV ltac:(clear - TLR; lia) HS) as (A & B & C & D & E & F & G).
    assert (B' : fast <= fc_nb tb st) by (destruct (Z.eq_dec fast 1) as [E1|N1]; [specialize (B E1); clear - B E1; lia | clear - A FR N1; lia]).
    clear B. repeat (split; [clear - A B' C D E F G; lia|]). clear - TL HS. nia.
  Qed.
  Lemma fd_rd_nb : forall mx st, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl ->
    rdval bsegs mx (wa (DT + 4 + 4 * st + 3)) 1 false = Z_to_bv 64 (fc_nb tb st).
  Proof.
    intros mx st MU WM HS. pose proof (fd_cellA st HS) as (_ & _ & _ & _ & _ & _ & L). open_an AN. pose proof TBV as (_ & _ & BY & _).
    destruct (fd_tbM mx MU WM) as [B _]. unfold fc_nb. replace (DT + 4 + 4 * st + 3) with (DT + 4 + (4 * st + 3)) by lia.
    apply (fd_rd1 mx (DT + 4) tb (4 * st + 3) B BY); clear - HS L; lia.
  Qed.
  Lemma fd_rd_sy : forall mx st, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl ->
    rdval bsegs mx (wa (DT + 4 + 4 * st + 2)) 1 false = Z_to_bv 64 (fc_sy tb st).
  Proof.
    intros mx st MU WM HS. pose proof (fd_cellA st HS) as (_ & _ & _ & _ & _ & _ & L). open_an AN. pose proof TBV as (_ & _ & BY & _).
    destruct (fd_tbM mx MU WM) as [B _]. unfold fc_sy. replace (DT + 4 + 4 * st + 2) with (DT + 4 + (4 * st + 2)) by lia.
    apply (fd_rd1 mx (DT + 4) tb (4 * st + 2) B BY); clear - HS L; lia.
  Qed.
  Lemma fd_rd_nx : forall mx st, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl ->
    rdval bsegs mx (wa (DT + 4 + 4 * st)) 2 false = Z_to_bv 64 (fc_nx tb st).
  Proof.
    intros mx st MU WM HS. pose proof (fd_cellA st HS) as (_ & _ & _ & _ & _ & _ & L). open_an AN. pose proof TBV as (_ & _ & BY & _).
    destruct (fd_tbM mx MU WM) as [B _]. unfold fc_nx. replace (DT + 4 + 4 * st) with (DT + 4 + (4 * st)) by lia.
    apply (fd_rd2 mx (DT + 4) tb (4 * st) B BY); clear - HS L; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma fd_rd_w2 : forall mx st, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl ->
    rdval bsegs mx (wa (DT + 4 + 4 * st + 2)) 2 false = Z_to_bv 64 (fc_sy tb st + 256 * fc_nb tb st).
  Proof.
    intros mx st MU WM HS. pose proof (fd_cellA st HS) as (_ & _ & _ & _ & _ & _ & L). open_an AN. pose proof TBV as (_ & _ & BY & _).
    destruct (fd_tbM mx MU WM) as [B _]. unfold fc_sy, fc_nb. replace (DT + 4 + 4 * st + 2) with (DT + 4 + (4 * st + 2)) by lia.
    replace (4 * st + 3) with (4 * st + 2 + 1) by lia.
    apply (fd_rd2 mx (DT + 4) tb (4 * st + 2) B BY); clear - HS L; lia.
  Qed.
  Lemma fd_tblen : zlen tb = 4 * 2^tl /\ zlen (map (Z_to_bv 8) tb) = 4 * 2^tl /\ Forall isbyte tb /\ zlen src = n.
  Proof. open_an AN. destruct TBV as (L & _ & BY & _). rewrite length_map. split; [exact L|]. split; [exact L|]. split; [exact BY| exact SRCLEN]. Qed.
  (* [comment removed for export] *)
  Lemma fd_rd_nbA : forall mx st a, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl -> a = DT + 4 + 4 * st + 3 ->
    rdval bsegs mx (wa a) 1 false = Z_to_bv 64 (fc_nb tb st).
  Proof. intros mx st a MU WM HS ->. apply fd_rd_nb; assumption. Qed.
  Lemma fd_rd_syA : forall mx st a, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl -> a = DT + 4 + 4 * st + 2 ->
    rdval bsegs mx (wa a) 1 false = Z_to_bv 64 (fc_sy tb st).
  Proof. intros mx st a MU WM HS ->. apply fd_rd_sy; assumption. Qed.
  Lemma fd_rd_nxA : forall mx st a, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl -> a = DT + 4 + 4 * st ->
    rdval bsegs mx (wa a) 2 false = Z_to_bv 64 (fc_nx tb st).
  Proof. intros mx st a MU WM HS ->. apply fd_rd_nx; assumption. Qed.
  Lemma fd_rd_w2A : forall mx st a, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> 0 <= st < 2^tl -> a = DT + 4 + 4 * st + 2 ->
    rdval bsegs mx (wa a) 2 false = Z_to_bv 64 (fc_sy tb st + 256 * fc_nb tb st).
  Proof. intros mx st a MU WM HS ->. apply fd_rd_w2; assumption. Qed.
  (* [comment removed for export] *)
  Lemma fd_tblinM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> tbl_in bsegs mx (DT + 4) (4 * 2^tl) 4 3 0 9.
  Proof.
    intros mx MU WM i I0 I1. open_hy HY.
    assert (HS : 0 <= i < 2^tl) by (clear - I0 I1; lia).
    pose proof (fd_cellA i HS) as (NB & _). replace (DT + 4 + 4 * i + 3) with (DT + 4 + 4 * i + 3) by reflexivity.
    rewrite (fd_rd_nb mx i MU WM HS). destruct TLR as [T1 T2]. open_an AN. destruct TBV as (_ & FR & _).
    rewrite unsigned_lit by (clear - NB FR T1 T2; lia). clear - NB FR T2. lia.
  Qed.
  Lemma fd_aro_maskM : forall mx, munch (FD_WB DST cap SPB) mA mx -> wmono bsegs mA mx -> aro RNG mx FBITMASK 128.
  Proof. intros mx MU WM. apply (aro_client_at _ _ _ _ (fd_acM mx MU WM)). cbn [ACLIENT_RO In]. do 30 right. left. reflexivity. Qed.
  Lemma fd_rd_mask : forall (mx : amem) nb a, mem_inv bsegs mx -> 0 <= nb <= 31 -> a = FBITMASK + 4 * nb -> rdval bsegs mx (wa a) 4 false = Z_to_bv 64 (2^nb - 1).
  Proof.
    intros mx nb a MI H ->. unfold rdval. rewrite (fbitmask_know mx nb MI H). cbn [extz].
    replace (word_to_le_bytes 4 (Z_to_bv 64 (2^nb - 1))) with (firstn 4 (skipn 0 (word_to_le_bytes 4 (Z_to_bv 64 (2^nb - 1))))) by reflexivity.
    rewrite (slice_word_bytes 4 0 4) by lia. apply bv_eq. rewrite !Z_to_bv_unsigned.
    assert (P : 0 < 2^nb <= 2^31) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_le_mono_r; lia]).
    unfold bv_wrap. cbn [bv_modulus Z.of_nat Z.of_N Z.mul Pos.mul]. rewrite Z.pow_0_r, Z.div_1_r.
    rewrite !Z.mod_small; [reflexivity | ..]; change (bv_modulus 64) with (2^64); change (2 ^ (8 * Z.of_nat 4)) with (2^32); rewrite ?Z.mod_small; lia.
  Qed.

End G.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fd_entst (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SPV SPB DST cap SRC n hs WK wksz DT FF : Z)
    (pc : Z) (mm : amem) (x1 x5 x6 x7 x10 x12 x13 x14 x16 x17 x28 x29 x30 x31 : word) : machine_state :=
  MS (mkR x1 (Z_to_bv 64 SPB) gp tp x5 x6 x7 (Z_to_bv 64 SPV) (Z_to_bv 64 SPB)
          x10 (Z_to_bv 64 (SRC + hs)) x12 x13 x14 (Z_to_bv 64 (n - hs)) x16 x17
          (Z_to_bv 64 FF) (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)) (Z_to_bv 64 0x22700) (Z_to_bv 64 DT) (Z_to_bv 64 n) (Z_to_bv 64 SRC)
          (Z_to_bv 64 (DST + cap)) (Z_to_bv 64 (DST + cap - 3)) (Z_to_bv 64 DST) (Z_to_bv 64 0x7fff8000) x28 x29 x30 x31)
     F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs).
(* [comment removed for export] *)
Definition fd_entK (RNG : footprint) (Q : machine_state -> Prop) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (mA : amem)
    (SPV SPB lo DST cap SRC n hs WK wksz DT FF : Z) (pc : Z) : Prop :=
  forall mm (x1 x5 x6 x7 x10 x12 x13 x14 x16 x17 x28 x29 x30 x31 : word) j1 j2 jb,
    rw_cells bsegs mm (SPB + 48) [CB 16 j2] -> rw_cells bsegs mm (SPB + 64) [CB 16 j1] -> rw_cells bsegs mm (SPB + 80) [CB 40 jb] ->
    stk bsegs mm DST (DST + cap) -> stk bsegs mm lo SPB -> mem_inv bsegs mm -> munch (FD_WB DST cap SPB) mA mm -> wmono bsegs mA mm ->
    evtF bsegs RNG Q (fd_entst gp tp F fc SPV SPB DST cap SRC n hs WK wksz DT FF pc mm x1 x5 x6 x7 x10 x12 x13 x14 x16 x17 x28 x29 x30 x31).
(* [comment removed for export] *)
Definition fl_ptr (SRC n hs ptr : Z) : Prop := ptr = SRC + hs \/ (SRC + hs <= ptr /\ ptr + 8 <= SRC + n).
End CANSEC1.

(* [comment removed for export] *)

Ltac open_hy HY := apply (fdA_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY); intros TLR DSTL CAP0 CAPH DSTH SRCL N0 NH SRCH HS1 HSN WKL WKSZ0 WKSZ WKH WKA DTE ROOM LO0 LOS SPR SPA KLO BOT SPB0 SPB1 SPBA OFFDST OFFWK OFFSRC DSTWK DSTSRC WKSRC F64 FFH FFT RFF RSFF FFDST FFWK FFSRC RSTK RI RDST RSDST ABD RSRC RSSRC ABS RWK RSWK ABW RSFR.
Ltac open_an AN := apply (fdA_an_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AN); intros UDj USj UWj AZj ARTj ACj DTHj TBj TBV WSj WKLOj SRCBj SRCLEN FAj FBj SK0j SK1j SK2j MIj.
Ltac open_fdm I := apply (FDM_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros S2 S1 BDC STD STL MI MU WM; unfold bitd_cells in BDC.
Ltac close_fdm := unfold bitd_cells; eapply FDM_close; unfold bitd_cells; eassumption.
Ltac open_fdms I := apply (FDMS_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros S2 S1 BDC STD STL MI MU WM.
Ltac close_fdms := eapply FDMS_close; eassumption.
(* [comment removed for export] *)
Ltac fd_atP HY AN :=
  pose proof (fd_bands _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (B_SPV & B_SPK & B_WK & B_SRC & B_WKI & B_SRCI & B_FFI & P2);
  pose proof (fd_tblen _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ AN) as (TBL & TBL' & TBY & SRCLEN);
  pose proof (fd_seps _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as (SP_DB & SP_DT & SP_DS & SP_BS & SP_BT & SP_BS2 & SP_BW);
  pose proof (fd_astk _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY) as ASTK.
Ltac fd_atM HY AN MU WM :=
  pose proof (fd_udM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU) as UD; pose proof (fd_usM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU) as US; pose proof (fd_uwM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU) as UW;
  pose proof (fd_azM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as AZ; pose proof (fd_artM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as ART; pose proof (fd_acM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as AC;
  pose proof (fd_dthM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as DTH; pose proof (fd_tbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as TB;
  pose proof (fd_wsM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as WS; pose proof (fd_wkloM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as WKLO;
  pose proof (fd_srcM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU) as SRCB;
  pose proof (fd_faM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as FA; pose proof (fd_fbM _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as FB;
  pose proof (fd_sk0M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as SK0; pose proof (fd_sk1M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as SK1; pose proof (fd_sk2M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN _ MU WM) as SK2.
Ltac fd_clearM DST SRC WK DT SPB :=
  repeat match goal with
         | H : unpoisoned _ _ _ |- _ => clear H | H : azstk _ _ _ _ |- _ => clear H | H : art _ |- _ => clear H | H : aro_client _ _ |- _ => clear H
         | H : rw_cells _ _ DT _ |- _ => clear H | H : u8arr _ _ (DT + 4) _ |- _ => clear H | H : stk _ _ (DT + 4 + _) _ |- _ => clear H
         | H : stk _ _ WK DT |- _ => clear H | H : bytes_at _ _ SRC _ |- _ => clear H | H : rw_cells _ _ (SPB + 8) _ |- _ => clear H
         | H : rw_cells _ _ (SPB + 40) _ |- _ => clear H | H : stk _ _ SPB (SPB + 8) |- _ => clear H | H : stk _ _ (SPB + 32) _ |- _ => clear H
         | H : stk _ _ (SPB + 120) _ |- _ => clear H
         end.
Ltac fd_at HY AN MU WM := fd_atP HY AN; fd_atM HY AN MU WM.

(* [comment removed for export] *)
Ltac fd_rdnb HY AN MU WM H st HS := lazymatch type of H with _ = rdval _ ?mx (wa ?a) 1 false =>
  rewrite (fd_rd_nbA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM HS ltac:(clear; lia)) in H end.
Ltac fd_rdnx HY AN MU WM H st HS := lazymatch type of H with _ = rdval _ ?mx (wa ?a) 2 false =>
  rewrite (fd_rd_nxA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM HS ltac:(clear; lia)) in H end.
Ltac fd_rdw2 HY AN MU WM H st HS := lazymatch type of H with _ = rdval _ ?mx (wa ?a) 2 false =>
  rewrite (fd_rd_w2A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HY AN mx st a MU WM HS ltac:(clear; lia)) in H end.
(* [comment removed for export] *)
Ltac fl_kz SRC n hs cap DST tl DT WK wksz SPB SPV := constr:(
  [KZRange SRC 4096 (2^47); KZRange (SRC + n) 4096 (2^47); KZRange n 0 65536; KZRange hs 1 65536;
   KZRange cap 0 65536; KZRange DST 4096 (2^47); KZRange (DST + cap) 4096 (2^47); KZRange (2^tl) 32 512; KZRange tl 5 9;
   KZRange DT 4096 (2^47); KZRange WK 4096 (2^47); KZRange (WK + wksz) 4096 (2^47); KZRange wksz 0 (2^32);
   KZRange SPB 17594333495296 (2^47 - 256); KZAlign SPB 32; KZRange SPV 17594333495296 (2^47 - 16);
   KZWr DST cap]).


(* [comment removed for export] *)
Ltac kx_abs_hyp H :=
  repeat match type of H with
         | context [ev ?E ?j] => let b := fresh "rb" in set (b := ev E j) in *; clearbody b
         | context [edenot ?E ?e] => let b := fresh "rw" in set (b := edenot E e) in *; clearbody b
         end.

(* [comment removed for export] *)
Ltac fd_rdS H :=
  kx_side_pre;
  lazymatch goal with
  | KXA : atoms_ok ?zs ?E |- rd_ok ?segs ?mm _ ?a ?nn =>
      let nz := kx_len zs in let P := kx_rd_fact segs mm H in
      eapply (kx_rd_ok segs mm E a nn _ _ P); kx_estarts E zs nz KXA; rewrite ?length_map; try (change (length fbitmask_bytes) with 128%nat); unfold FBITMASK; kx_lia
  end.
(* [comment removed for export] *)
Lemma fuland_mask_lt2 : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x (2^nb - 1) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  replace (2^nb - 1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. exact P.
Qed.

