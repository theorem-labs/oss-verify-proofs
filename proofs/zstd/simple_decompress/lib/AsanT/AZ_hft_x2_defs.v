(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit FseWalkMem MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufWM ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF StepF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import KXExec KXSound KXFull KXBridge KXTac KXGo KXTree KXAuto KXMem KXMem2 KXPost KXGoF KXLean KXAsanF KXAutoAF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface AZ_kx AZ_hft_x1_defs AZ_hft_x2_geo AZ_hft_x2h_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanW Require Import AZ_wt_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RZ_hft_x1_kit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations. Import KXS.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Notation zlen l := (Z.of_nat (length l)).
Notation isbyte := (fun v : Z => 0 <= v < 256).

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition x2A_hyps (RNG : footprint) (SPV SPA lo DT WK wksz FF : Z) : Prop :=
  4096 <= DT
  /\ DT + 16388 <= 2^47
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
  /\ SPV - 848 <= SPA <= SPV - 832
  /\ SPA mod 32 = 0
  /\ (DT + 16388 <= lo \/ SPV <= DT)
  /\ (WK + wksz <= lo \/ SPV <= WK)
  /\ (DT + 16388 <= WK \/ WK + wksz <= DT)
  /\ FF mod 64 = 0
  /\ 4096 <= FF
  /\ FF + 64 <= ATOP
  /\ ablk FF (FF + 64)
  /\ (DT + 16388 <= FF \/ FF + 64 <= DT)
  /\ (WK + wksz <= FF \/ FF + 64 <= WK)
  /\ ablk DT (DT + 16388)
  /\ rng RNG DT 16388
  /\ rng RNG (shad DT) (shspan DT 16388)
  /\ ablk WK (WK + wksz)
  /\ rng RNG WK wksz
  /\ rng RNG (shad WK) (shspan WK wksz)
  /\ rng RNG FF 64
  /\ rng RNG lo (SPV - lo)
  /\ rng_aimg RNG.

Lemma x2A_open : forall RNG SPV SPA lo DT WK wksz FF, x2A_hyps RNG SPV SPA lo DT WK wksz FF ->
  forall G : Prop, (4096 <= DT ->
    DT + 16388 <= 2^47 ->
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
    SPV - 848 <= SPA <= SPV - 832 ->
    SPA mod 32 = 0 ->
    (DT + 16388 <= lo \/ SPV <= DT) ->
    (WK + wksz <= lo \/ SPV <= WK) ->
    (DT + 16388 <= WK \/ WK + wksz <= DT) ->
    FF mod 64 = 0 ->
    4096 <= FF ->
    FF + 64 <= ATOP ->
    ablk FF (FF + 64) ->
    (DT + 16388 <= FF \/ FF + 64 <= DT) ->
    (WK + wksz <= FF \/ FF + 64 <= WK) ->
    ablk DT (DT + 16388) ->
    rng RNG DT 16388 ->
    rng RNG (shad DT) (shspan DT 16388) ->
    ablk WK (WK + wksz) ->
    rng RNG WK wksz ->
    rng RNG (shad WK) (shspan WK wksz) ->
    rng RNG FF 64 ->
    rng RNG lo (SPV - lo) ->
    rng_aimg RNG -> G) -> G.
Proof. intros until FF. intros HY G K. destruct HY as (Y0 & Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13 & Y14 & Y15 & Y16 & Y17 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Y28 & Y29 & Y30 & Y31). eapply K; eassumption. Qed.
Ltac open_hx2 HY := apply (x2A_open _ _ _ _ _ _ _ _ HY); intros DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.

(* [comment removed for export] *)
Definition X2F (FF DT WK : Z) (k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 : word) : list cell :=
  [C8 k0; C8 k8; C8 k16; C8 k24; C8 k32; C8 k40;
   C8 k48; C8 (Z_to_bv 64 (Z.shiftr DT 3 + 2147450880)); C8 k64; C8 k72; C8 k80; C8 k88;
   C8 (Z_to_bv 64 (Z.shiftr FF 3 + 2147450880)); C8 k104; C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 FF); C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 WK);
   C8 k144; C8 k152; C8 k160; C8 k168; C8 k176; C8 k184;
   C8 k192; C8 k200; C8 k208; C8 k216; C8 k224; C8 k232;
   C8 k240; C8 k248; C8 k256; C8 k264; C8 k272; C8 k280;
   C8 k288; C8 k296; C8 k304; C8 k312; C8 k320; C8 k328;
   C8 k336; C8 k344; C8 k352; C8 k360; C8 k368; C8 k376;
   C8 k384; C8 k392; C8 k400; C8 k408; C8 k416; C8 k424;
   C8 k432; C8 k440; C8 k448; C8 k456; C8 k464; C8 k472;
   C8 k480; C8 k488; C8 k496; C8 k504; C8 k512; C8 k520;
   C8 k528; C8 k536; C8 k544; C8 k552; C8 k560; C8 k568;
   C8 k576; C8 k584; C8 k592; C8 k600; C8 k608; C8 k616;
   C8 k624; C8 k632; C8 k640; C8 k648; C8 k656; C8 k664;
   C8 k672; C8 k680; C8 k688; C8 k696; C8 k704; C8 k712;
   C8 (Z_to_bv 64 FF)].
(* [comment removed for export] *)
Ltac x2_wordify_go H segs m A pre rest :=
  lazymatch rest with
  | CB 8 ?j :: ?post =>
      let w := fresh "w" in let H' := fresh "WH" in
      destruct (cb8_as_c8 segs m A pre j post H) as [w H']; clear H; rename H' into H;
      let pre' := eval cbn [app] in (pre ++ [C8 w]) in x2_wordify_go H segs m A pre' post
  | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in x2_wordify_go H segs m A pre' post
  | nil => cbn [app] in H
  end.
Ltac x2_wordify H := lazymatch type of H with rw_cells ?segs ?m ?A ?cs => x2_wordify_go H segs m A (@nil cell) cs end.
Ltac x2_split8_go H segs m A pre rest :=
  lazymatch rest with
  | CB 8 ?j :: ?post => let pre' := eval cbn [app] in (pre ++ [CB 8 j]) in x2_split8_go H segs m A pre' post
  | CB ?n ?j :: ?post =>
      let sz := eval vm_compute in (List.repeat 8%nat (Nat.div n 8)) in
      apply (rw_cells_split_CB segs m A pre n j post sz) in H; [| reflexivity]; cbn [mk_CB_cells app] in H
  | ?c :: ?post => let pre' := eval cbn [app] in (pre ++ [c]) in x2_split8_go H segs m A pre' post
  end.
Ltac x2_split8 H := repeat lazymatch type of H with rw_cells ?segs ?m ?A ?cs => x2_split8_go H segs m A (@nil cell) cs end.
(* [comment removed for export] *)
Lemma X2FRA_as_F : forall m SPA FF DT WK hdw jA jB jC jD, rw_cells bsegs m SPA (X2FRA FF DT WK hdw jA jB jC jD) ->
  exists k0 k8 k16 k24 k32 k40 k48 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712,
    rw_cells bsegs m SPA (X2F FF DT WK k0 k8 k16 k24 k32 k40 k48 (Z_to_bv 64 hdw) k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712).
Proof.
  intros m SPA FF DT WK hdw jA jB jC jD H. unfold X2FRA in H.
  x2_split8 H.
  x2_wordify H.
  unfold X2F. do 83 eexists. exact H.
Qed.

(* [comment removed for export] *)
Definition XB (m5 : amem) (SPV SPA lo DT WK wksz FF nbs : Z) (hw rank : list Z) (k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 : word) (dt rs0 : list Z) (syb : list byte) (rv : list Z) (m1 : amem) : Prop :=
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt)
  /\ zlen dt = 16388
  /\ Forall isbyte dt
  /\ u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw)
  /\ u8arr bsegs m1 (WK + 624) (map (Z_to_bv 8) (u32b rank))
  /\ u8arr bsegs m1 (WK + 676) (map (Z_to_bv 8) (u32b rs0))
  /\ zlen rs0 = 15
  /\ Forall (fun v : Z => 0 <= v) rs0
  /\ u8arr bsegs m1 (WK + 736) syb
  /\ zlen syb = 256
  /\ u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rv))
  /\ zlen rv = 156
  /\ Forall (fun v : Z => 0 <= v) rv
  /\ stk bsegs m1 (WK + 1248) (WK + wksz)
  /\ rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)]
  /\ stk bsegs m1 lo SPA
  /\ mem_inv bsegs m1
  /\ munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 848, SPA + 728)] m5 m1
  /\ wmono bsegs m5 m1
  /\ rw_cells bsegs m1 SPA (X2F FF DT WK k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712).

Lemma XB_open : forall m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs0 syb rv m1,
  XB m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs0 syb rv m1 ->
  forall G : Prop, (u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
    zlen dt = 16388 ->
    Forall isbyte dt ->
    u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw) ->
    u8arr bsegs m1 (WK + 624) (map (Z_to_bv 8) (u32b rank)) ->
    u8arr bsegs m1 (WK + 676) (map (Z_to_bv 8) (u32b rs0)) ->
    zlen rs0 = 15 ->
    Forall (fun v : Z => 0 <= v) rs0 ->
    u8arr bsegs m1 (WK + 736) syb ->
    zlen syb = 256 ->
    u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rv)) ->
    zlen rv = 156 ->
    Forall (fun v : Z => 0 <= v) rv ->
    stk bsegs m1 (WK + 1248) (WK + wksz) ->
    rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)] ->
    stk bsegs m1 lo SPA ->
    mem_inv bsegs m1 ->
    munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 848, SPA + 728)] m5 m1 ->
    wmono bsegs m5 m1 ->
    rw_cells bsegs m1 SPA (X2F FF DT WK k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712) -> G) -> G.
Proof. intros until m1. intros I G K. destruct I as (H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15 & H16 & H17 & H18 & FR). eapply K; eassumption. Qed.
Ltac open_xb I := apply (XB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RS0 RS0LEN RS0NN SYC SYLEN RV RVLEN RVNN WKR NBC STK MI MU WM FR; unfold X2F in FR.
Lemma XB_close : forall m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs0 syb rv m1,
  u8arr bsegs m1 DT (map (Z_to_bv 8) dt) ->
  zlen dt = 16388 ->
  Forall isbyte dt ->
  u8arr bsegs m1 (WK + 992) (map (Z_to_bv 8) hw) ->
  u8arr bsegs m1 (WK + 624) (map (Z_to_bv 8) (u32b rank)) ->
  u8arr bsegs m1 (WK + 676) (map (Z_to_bv 8) (u32b rs0)) ->
  zlen rs0 = 15 ->
  Forall (fun v : Z => 0 <= v) rs0 ->
  u8arr bsegs m1 (WK + 736) syb ->
  zlen syb = 256 ->
  u8arr bsegs m1 WK (map (Z_to_bv 8) (u32b rv)) ->
  zlen rv = 156 ->
  Forall (fun v : Z => 0 <= v) rv ->
  stk bsegs m1 (WK + 1248) (WK + wksz) ->
  rw_cells bsegs m1 (FF + 48) [C4 (Z_to_bv 64 nbs)] ->
  stk bsegs m1 lo SPA ->
  mem_inv bsegs m1 ->
  munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 848, SPA + 728)] m5 m1 ->
  wmono bsegs m5 m1 ->
  rw_cells bsegs m1 SPA (X2F FF DT WK k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712) ->
  XB m5 SPV SPA lo DT WK wksz FF nbs hw rank k0 k8 k16 k24 k32 k40 k48 k64 k72 k80 k88 k104 k144 k152 k160 k168 k176 k184 k192 k200 k208 k216 k224 k232 k240 k248 k256 k264 k272 k280 k288 k296 k304 k312 k320 k328 k336 k344 k352 k360 k368 k376 k384 k392 k400 k408 k416 k424 k432 k440 k448 k456 k464 k472 k480 k488 k496 k504 k512 k520 k528 k536 k544 k552 k560 k568 k576 k584 k592 k600 k608 k616 k624 k632 k640 k648 k656 k664 k672 k680 k688 k696 k704 k712 dt rs0 syb rv m1.
Proof. intros. unfold XB. repeat (split; [eassumption|]). eassumption. Qed.
Ltac close_xb := unfold X2F; eapply XB_close; try eassumption.

(* [comment removed for export] *)
Definition TT (tl : Z) : Z := if tl <? 12 then 11 else 12.

Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?u32b_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.

Section G.
  Variables (RNG : footprint) (m5 : amem) (SPV SPA lo DT WK wksz FF : Z).
  Hypothesis HY : x2A_hyps RNG SPV SPA lo DT WK wksz FF.
  Hypothesis UDT : unpoisoned m5 DT (DT + 16388).
  Hypothesis UW : unpoisoned m5 WK (WK + wksz).
  Hypothesis ART0 : art m5.

  (* [comment removed for export] *)
  Lemma x2_bands : (DT + 16388 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= DT) /\ (WK + wksz + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= WK)
                   /\ 0x10007fff8000 + 5072 <= SPA /\ SPA + 848 <= 2^47 /\ 0x625000 <= DT /\ 0x625000 <= WK
                   /\ FF + 64 + 4096 <= lo /\ (FF + 64 + 8 <= 0x7fff8000 \/ 0x10007fff8000 <= FF).
  Proof.
    open_hx2 HY. clear SDS SWS DTWK DFD DFW.
    pose proof ATOP_range as ATR. unfold ATOP_MIN, ATOP_MAX in ATR. unfold ablk, AIMG_HI, KLS in ABD, ABW, ABF. unfold KHIGH in KLO.
    repeat split; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_unp_dtM : forall m1, munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 848, SPA + 728)] m5 m1 -> unpoisoned m1 DT (DT + 16388).
  Proof.
    intros m1 MU. open_hx2 HY. clear SDS SWS DTWK DFD DFW. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UDT | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear ABD ABW ABF. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2_unp_wkM : forall m1, munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 848, SPA + 728)] m5 m1 -> unpoisoned m1 WK (WK + wksz).
  Proof.
    intros m1 MU. open_hx2 HY. clear SDS SWS DTWK DFD DFW. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply unpoisoned_munch; [exact UW | exact MU |].
    cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF in *. clear ABD ABW ABF. repeat split; Z.div_mod_to_equations; lia.
  Qed.
  Lemma x2_artM : forall m1, munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 848, SPA + 728)] m5 m1 -> wmono bsegs m5 m1 -> art m1.
  Proof.
    intros m1 MU WM. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    eapply x2h_art_transport; [exact ART0| exact MU| exact WM|]. open_hx2 HY. unfold ablk, AIMG_HI in ABF. repeat constructor; cbn [fst]; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma x2_helper_hyps : x2hA_hyps RNG SPA DT (WK + 736).
  Proof.
    open_hx2 HY. pose proof x2_bands as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8).
    assert (A1 : 4096 <= WK + 736) by lia. assert (A2 : WK + 736 + 256 < 2^47) by lia.
    assert (A3 : KHIGH <= SPA) by (unfold KHIGH in *; lia). assert (A4 : SPA + 728 <= 2^47) by lia.
    assert (A5 : SPA mod 16 = 0) by (clear - SPA32; Z.div_mod_to_equations; lia).
    assert (A6 : DT + 16388 <= WK + 736 \/ WK + 736 + 256 <= DT) by (clear - DTWK WR; lia).
    assert (A7 : DT + 16388 <= SPA \/ SPA + 728 <= DT) by (clear - SDS LOS SPAB; lia).
    assert (A8 : WK + 736 + 256 <= SPA \/ SPA + 728 <= WK + 736) by (clear - SWS LOS SPAB WR; lia).
    assert (A9 : ablk (WK + 736) (WK + 736 + 256)) by (eapply ablk_sub; [exact ABW| lia| lia]).
    assert (A10 : rng RNG (WK + 736) 256) by (eapply rng_sub; [exact RW| lia| lia]).
    assert (A11 : rng RNG (shad (WK + 736)) (shspan (WK + 736) 256))
      by (destruct (shspan_sub WK wksz (WK + 736) 256 ltac:(lia) ltac:(lia) ltac:(lia)) as [S1 S2]; eapply rng_sub; [exact RSW| exact S1| lia]).
    assert (A12 : rng RNG SPA 728) by (eapply rng_sub; [exact RSTK| lia| lia]).
    exact (conj DTL (conj DTH (conj DT4 (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8
          (conj ABD (conj RDT (conj RSDT (conj A9 (conj A10 (conj A11 (conj A12 RI)))))))))))))))))).
  Qed.
End G.
End CANSEC1.

(* [comment removed for export] *)

Ltac open_hx2 HY := apply (x2A_open _ _ _ _ _ _ _ _ HY); intros DTL DTH DT4 WKL WKH WK4 WR KLO BOT LOS SPT SP16 SPAB SPA32 SDS SWS DTWK F64 FFL FC ABF DFD DFW ABD RDT RSDT ABW RW RSW RFF RSTK RI.
Ltac open_xb I := apply (XB_open _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ I); intros DTC DTLEN DTBY HWC RK RS0 RS0LEN RS0NN SYC SYLEN RV RVLEN RVNN WKR NBC STK MI MU WM FR; unfold X2F in FR.
Ltac close_xb := unfold X2F; eapply XB_close; try eassumption.
Ltac simpl_arr_sizes ::= rewrite ?u32s_length, ?u64s_length, ?upd_length, ?u16s_length, ?length_map, ?u32b_length,
                                  ?FseLemmas.upd_nat_length, ?FseLemmas.Zupd_length in *.
