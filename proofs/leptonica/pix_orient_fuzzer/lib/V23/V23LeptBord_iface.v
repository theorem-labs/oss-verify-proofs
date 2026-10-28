(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomBL LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptPixCreate O23LeptPixCopy O23LeptGrayA O23LeptBord_iface.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptPixHdr V23LeptPixCreate V23LeptPixCopy V23LeptGrayA V23LeptRop_iface V23LeptRop2_iface.
Import ListNotations.
Open Scope bv_scope.

Section BordIface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition pixAddBorderGeneral2_contract : Prop :=
  forall C A m md regs (s pixs w h d datas spp rc fmt spc txt left right top bot val : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ABG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
  PIXat m pixs (hdvg w h d datas spp rc fmt spc txt) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 1 \/ d = 8)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z ->
  (1 <= left <= 64)%Z -> (1 <= right <= 64)%Z -> (1 <= top <= 64)%Z -> (1 <= bot <= 64)%Z ->
  rop2_arm (left * d)%Z (0 * d)%Z (w * d)%Z (wpl_of w d) ->
  (val = 0 \/ val = 2 ^ d - 1)%Z -> ((w + left + right) * (h + top + bot) <= 400000000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_abg w h d left right top bot <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (w + left + right) (h + top + bot) d /\
                             pix_fresh C A A' m' pixd (w + left + right) (h + top + bot) d data) ) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_abg w h d left right top bot) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixAddBorderGeneral) m al_rom) md) S.

End BordIface.
