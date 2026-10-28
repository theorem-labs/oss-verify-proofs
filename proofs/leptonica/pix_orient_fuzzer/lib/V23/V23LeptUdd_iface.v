(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoomBL LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptSelGP.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptMbc.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Iface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition PC_UDD : Z := 719008.

(* [comment removed for export] *)
Definition udd_src (C : lctx) (A : AS) (m : word -> option byte) (pixs w h cm datas : Z) (cv : cmapv) : Prop :=
  pixs = 0%Z \/
  ( PIXat m pixs (hdv w h 1 cm datas) /\ hdr_ok w h 1 /\ (1 <= w)%Z /\ (1 <= h)%Z /\
    live A (Z_to_bv 64 pixs) = Some 64%Z /\ live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z /\
    live (c_A0 C) (Z_to_bv 64 pixs) = None /\ live (c_A0 C) (Z_to_bv 64 datas) = None /\
    (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z /\
                  live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None)) ).

Definition pixUpDownDetect_contract (STK RK : Z) (RB : Z -> Z -> Z -> Z) : Prop :=
  forall fr cs C A m md regs (s pixs pconf w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs -> MBC C ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + STK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 1278416 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 pconf -> getr regs 12 = Z_to_bv 64 0 -> getr regs 13 = Z_to_bv 64 0 ->
  getr regs 14 = Z_to_bv 64 0 ->
  (s <= pconf)%Z -> (pconf + 4 <= c_top C)%Z -> (pconf mod 4 = 0)%Z ->
  udd_src C A m pixs w h cm datas cv ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK <= kR)%Z -> (RB w h cm <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs' (y : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' ->
     POSTM C A s (wr4 m pconf y) m' -> (forall q, live A' q = live A q) ->
     aroom A' vm' (kR - RK) (bR - RB w h cm) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_UDD) m al_rom) md) S.

End Iface.
