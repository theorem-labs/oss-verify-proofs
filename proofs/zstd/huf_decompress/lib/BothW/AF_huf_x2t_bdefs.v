(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image Frame.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXMem KXTac KXGo KXPost KXFoot KXGoF KXChk KXGoM.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF Shadow StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg RtCells ABase.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.

Definition x2B_hyps (RNG : footprint) (SPV SPA lo DT WK wksz FF mtl : Z) : Prop :=
  1 <= mtl <= 12
  /\ 4096 <= DT
  /\ DT + (4 * (1 + 2 ^ mtl)) <= 2^47
  /\ DT mod 4 = 0
  /\ 4096 <= WK
  /\ WK + wksz < 2^47
  /\ WK mod 4 = 0
  /\ 2124 <= wksz < 2^32
  /\ KHIGH <= lo
  /\ ATOP + 4096 <= lo
  /\ lo <= SPV - 5936
  /\ SPV + 16 <= 2^47
  /\ SPV mod 16 = 0
  /\ SPV - 528 <= SPA <= SPV - 512
  /\ SPA mod 32 = 0
  /\ (DT + (4 * (1 + 2 ^ mtl)) <= lo \/ SPV <= DT)
  /\ (WK + wksz <= lo \/ SPV <= WK)
  /\ (DT + (4 * (1 + 2 ^ mtl)) <= WK \/ WK + wksz <= DT)
  /\ FF mod 64 = 0
  /\ 4096 <= FF
  /\ FF + 64 <= ATOP
  /\ ablk FF (FF + 64)
  /\ (DT + (4 * (1 + 2 ^ mtl)) <= FF \/ FF + 64 <= DT)
  /\ (WK + wksz <= FF \/ FF + 64 <= WK)
  /\ ablk DT (DT + (4 * (1 + 2 ^ mtl)))
  /\ rng RNG DT (4 * (1 + 2 ^ mtl))
  /\ rng RNG (shad DT) (nshad ((4 * (1 + 2 ^ mtl)) + DT mod 8))
  /\ ablk WK (WK + wksz)
  /\ rng RNG WK wksz
  /\ rng RNG (shad WK) (nshad (wksz + WK mod 8))
  /\ rng RNG FF 64
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG.

Lemma x2B_open : forall RNG SPV SPA lo DT WK wksz FF mtl, x2B_hyps RNG SPV SPA lo DT WK wksz FF mtl ->
  forall G : Prop, (1 <= mtl <= 12 ->
    4096 <= DT ->
    DT + (4 * (1 + 2 ^ mtl)) <= 2^47 ->
    DT mod 4 = 0 ->
    4096 <= WK ->
    WK + wksz < 2^47 ->
    WK mod 4 = 0 ->
    2124 <= wksz < 2^32 ->
    KHIGH <= lo ->
    ATOP + 4096 <= lo ->
    lo <= SPV - 5936 ->
    SPV + 16 <= 2^47 ->
    SPV mod 16 = 0 ->
    SPV - 528 <= SPA <= SPV - 512 ->
    SPA mod 32 = 0 ->
    (DT + (4 * (1 + 2 ^ mtl)) <= lo \/ SPV <= DT) ->
    (WK + wksz <= lo \/ SPV <= WK) ->
    (DT + (4 * (1 + 2 ^ mtl)) <= WK \/ WK + wksz <= DT) ->
    FF mod 64 = 0 ->
    4096 <= FF ->
    FF + 64 <= ATOP ->
    ablk FF (FF + 64) ->
    (DT + (4 * (1 + 2 ^ mtl)) <= FF \/ FF + 64 <= DT) ->
    (WK + wksz <= FF \/ FF + 64 <= WK) ->
    ablk DT (DT + (4 * (1 + 2 ^ mtl))) ->
    rng RNG DT (4 * (1 + 2 ^ mtl)) ->
    rng RNG (shad DT) (nshad ((4 * (1 + 2 ^ mtl)) + DT mod 8)) ->
    ablk WK (WK + wksz) ->
    rng RNG WK wksz ->
    rng RNG (shad WK) (nshad (wksz + WK mod 8)) ->
    rng RNG FF 64 ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG -> G) -> G.
Proof. intros until mtl. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31 & Y32). apply K; assumption. Qed.

Definition X2BF (FF DT WK : Z) (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word) : list cell :=
  [C8 k0; C8 k8; C8 k16; C8 k24; C8 k32; C8 k40;
   C8 k48; C8 k56; C8 k64; C8 k72; C8 k80; C8 k88;
   C8 k96; C8 k104; C8 k112; C8 k120; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); C8 k136;
   C8 k144; C8 k152; C8 k160; C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF);
   C8 k192; C8 (Z_to_bv 64 (WK + 676)); C8 k208; C8 (Z_to_bv 64 DT); C8 k224; C8 k232;
   C8 k240; C8 k248; C8 k256; C8 k264; C8 k272; C8 k280;
   C8 k288; C8 k296; C8 k304; C8 k312; C8 k320; C8 k328;
   C8 k336; C8 k344; C8 (Z_to_bv 64 WK); C8 k360; C8 k368; C8 k376;
   C8 k384; C8 k392; C8 (Z_to_bv 64 FF)].

Definition XBB (m5 : amem) (SPV SPA lo DT WK wksz FF mtl nbs : Z) (hw rank : list Z) (k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 : word) (dt rs0 : list Z) (syb : list byte) (rv : list Z) (m1 : amem) : Prop :=
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
  /\ zlen dt = (4 * (1 + 2 ^ mtl))
  /\ Forall isbyte dt
  /\ u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)
  /\ u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank)
  /\ u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0)
  /\ zlen rs0 = 15
  /\ Forall (fun v : Z => 0 <= v < 2^32) rs0
  /\ u8arr bsegs m1 (WK + 736) syb
  /\ zlen syb = 256
  /\ u32arr bsegs m1 WK (map (Z_to_bv 64) rv)
  /\ zlen rv = 156
  /\ Forall (fun v : Z => 0 <= v < 2^32) rv
  /\ stk bsegs m1 (WK + 1248) (WK + wksz)
  /\ rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]
  /\ stk bsegs m1 lo SPA
  /\ mem_inv bsegs m1
  /\ munch [(DT, DT + (4 * (1 + 2 ^ mtl))); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1
  /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X2BF FF DT WK k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392).

Lemma XBB_open : forall m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt rs0 syb rv m1,
  XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt rs0 syb rv m1 ->
  forall G : Prop, (u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
    zlen dt = (4 * (1 + 2 ^ mtl)) ->
    Forall isbyte dt ->
    u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw) ->
    u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank) ->
    u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0) ->
    zlen rs0 = 15 ->
    Forall (fun v : Z => 0 <= v < 2^32) rs0 ->
    u8arr bsegs m1 (WK + 736) syb ->
    zlen syb = 256 ->
    u32arr bsegs m1 WK (map (Z_to_bv 64) rv) ->
    zlen rv = 156 ->
    Forall (fun v : Z => 0 <= v < 2^32) rv ->
    stk bsegs m1 (WK + 1248) (WK + wksz) ->
    rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)] ->
    stk bsegs m1 lo SPA ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + (4 * (1 + 2 ^ mtl))); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1 ->
    wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X2BF FF DT WK k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392) -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & H19). apply K; assumption. Qed.

Lemma XBB_close : forall m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt rs0 syb rv m1,
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
  zlen dt = (4 * (1 + 2 ^ mtl)) ->
  Forall isbyte dt ->
  u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw) ->
  u32arr bsegs m1 (WK + 624) (map (Z_to_bv 64) rank) ->
  u32arr bsegs m1 (WK + 676) (map (Z_to_bv 64) rs0) ->
  zlen rs0 = 15 ->
  Forall (fun v : Z => 0 <= v < 2^32) rs0 ->
  u8arr bsegs m1 (WK + 736) syb ->
  zlen syb = 256 ->
  u32arr bsegs m1 WK (map (Z_to_bv 64) rv) ->
  zlen rv = 156 ->
  Forall (fun v : Z => 0 <= v < 2^32) rv ->
  stk bsegs m1 (WK + 1248) (WK + wksz) ->
  rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)] ->
  stk bsegs m1 lo SPA ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + (4 * (1 + 2 ^ mtl))); (WK, WK + wksz); (SPV - 640, SPA + 408)] m5 m1 ->
  wmono bsegs m5 m1 ->
  rw_cells bsegs m1 SPA (X2BF FF DT WK k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392) ->
  XBB m5 SPV SPA lo DT WK wksz FF mtl nbs hw rank k0 k8 k16 k24 k32 k40 k48 k56 k64 k72 k80 k88 k96 k104 k112 k120 k136 k144 k152 k160 k192 k208 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k360 k368 k376 k384 k392 dt rs0 syb rv m1.
Proof. intros. unfold XBB. repeat (split; [assumption|]). assumption. Qed.

Definition TTB (tl mtl : Z) : Z := if (tl <=? 11) && (11 <? mtl) then 11 else mtl.

Lemma TTB_range : forall tl mtl, 1 <= tl <= mtl -> mtl <= 12 -> tl <= TTB tl mtl <= mtl /\ Z.min mtl 11 <= TTB tl mtl.
Proof. intros tl mtl H1 H2. unfold TTB. destruct (Z.leb_spec tl 11), (Z.ltb_spec 11 mtl); cbn [andb]; lia. Qed.

Lemma TTB_12 : forall tl, 1 <= tl <= 12 -> TTB tl 12 = if tl <? 12 then 11 else 12.
Proof. intros tl H. unfold TTB. destruct (Z.leb_spec tl 11), (Z.ltb_spec tl 12); cbn; lia. Qed.

Lemma x2b_dtbB : forall mtl, 1 <= mtl <= 12 -> 8 <= 4 * (1 + 2 ^ mtl) <= 16388 /\ 2 <= 2 ^ mtl <= 4096.
Proof.
  intros mtl H.
  pose proof (Z.pow_le_mono_r 2 1 mtl ltac:(lia) ltac:(lia)) as P1.
  pose proof (Z.pow_le_mono_r 2 mtl 12 ltac:(lia) ltac:(lia)) as P2.
  change (2 ^ 1) with 2 in P1. change (2 ^ 12) with 4096 in P2. lia.
Qed.

End CANSEC1.

Ltac open_hx2b HY := apply (x2B_open _ _ _ _ _ _ _ _ _ HY); intros MTL DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.

Ltac open_xbb I := apply (XBB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RS0 RS0LEN RS0NN SYC SYLEN RV RVLEN RVNN WKR NBC STK MI MU WM FR; unfold X2BF in FR.

Ltac close_xbb := unfold X2BF; eapply XBB_close; try eassumption.
