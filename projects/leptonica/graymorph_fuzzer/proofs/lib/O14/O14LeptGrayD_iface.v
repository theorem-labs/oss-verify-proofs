(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptBase O14LeptPixHdr O14LeptPixCopy.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition SBV_STACK : Z := 112 + 16 + LSF.     (* [comment removed for export] *)
Definition G3H_STACK : Z := 160 + 176 + 16 + LSF.   (* [comment removed for export] *)

Definition PC_pixSetBorderVal : Z := 0x17344.
Definition PC_pixErodeGray3h : Z := 0x20004.
Definition PC_pixDilateGray3h : Z := 0x20854.


Section GrayDIface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.

(* [comment removed for export] *)
Definition gray8_shape (w h : Z) : Prop := (1 <= w)%Z /\ (1 <= h)%Z /\ hdr_ok w h 8.

(* [comment removed for export] *)
Definition pixSetBorderVal_contract : Prop :=
  forall C Ar A m md regs (s pixs w h cm data left right top bot val : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SBV_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 left -> getr regs 12 = Z_to_bv 64 right ->
  getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 val ->
  (1 <= left < w)%Z -> (1 <= right < w)%Z -> (1 <= top)%Z -> (1 <= bot)%Z -> (top + bot < h)%Z -> (0 <= val < 2 ^ 64)%Z ->
  PIXat m pixs (hdv w h 8 cm data) -> gray8_shape w h ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  Z_to_bv 64 pixs <> Z_to_bv 64 data ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixs (hdv w h 8 cm data) ->
      (forall a : word, ~ (s - SBV_STACK <= bv_unsigned a < s)%Z -> ~ (data <= bv_unsigned a < data + 4 * (wpl_of w 8 * h))%Z -> m' a = m a) ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixSetBorderVal) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixSetBorderVal_null_contract : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SBV_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 1 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixSetBorderVal) m al_rom) md) S.

(* [comment removed for export] *)
Definition PC_pixCreateTemplate : Z := 0x15c44.
Definition TP14 : Z := 0x3be10.
Definition PCT_STACK : Z := 16 + 128 + 16 + LSF.     (* [comment removed for export] *)
Definition pixCreateTemplate_sure_contract (RKt RBt : Z) : Prop :=
  forall C A m md regs (s pixs w h d datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCT_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP14 ->
  getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h d 0 datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->        (* [comment removed for export] *)
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RKt <= kR)%Z -> (RBt <= bR)%Z ->
  (forall A' m' vm' regs' pixd data, W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      getr regs' 10 = Z_to_bv 64 pixd -> pixt_new C A A' m' pixd w h d 0 data cv ->
      aroom A' vm' (kR - RKt) (bR - RBt) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixCreateTemplate) m al_rom) md) S.

(* [comment removed for export] *)
Definition gray3h_contract (entry RKt RBt : Z) : Prop :=
  forall C A m md regs (s pixs w h data : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + G3H_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP14 -> getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h 8 0 data) -> gray8_shape w h ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RKt <= kR)%Z -> (RBt <= bR)%Z ->
  (forall A' m' vm' regs' pixd datad, W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      getr regs' 10 = Z_to_bv 64 pixd -> pixt_new C A A' m' pixd w h 8 0 datad cv ->
      PIXat m' pixs (hdv w h 8 0 data) ->
      aroom A' vm' (kR - RKt) (bR - RBt) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 entry) m al_rom) md) S.
Definition pixErodeGray3h_contract := gray3h_contract PC_pixErodeGray3h.
Definition pixDilateGray3h_contract := gray3h_contract PC_pixDilateGray3h.

(* [comment removed for export] *)
Definition gray3h_null_contract (entry : Z) : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + G3H_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 entry) m al_rom) md) S.

End GrayDIface.
(* [comment removed for export] *)
