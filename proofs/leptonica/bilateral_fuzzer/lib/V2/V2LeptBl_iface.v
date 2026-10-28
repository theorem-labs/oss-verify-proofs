(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixHdr V2LeptPixCreate.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition AMB_STACK : Z := 1024 + 112 + LSF.   (* [comment removed for export] *)
Definition GEV_STACK : Z := 256.                (* [comment removed for export] *)
Definition PC_pixAddMirroredBorder : Z := 115776.
Definition PC_pixGetExtremeValue : Z := 125864.
(* [comment removed for export] *)
Definition RB_amb (w h b : Z) : Z := RB_pixT (4 * (wpl_of (w + 2 * b) 8 * (h + 2 * b))).

Section BlIface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition bl_src (A : AS) (m : word -> option byte) (pixs : Z) (v : pixv) : Prop :=
  PIXat m pixs v /\ p_d v = 8%Z /\ p_cmap v = 0%Z /\ hdr_ok (p_w v) (p_h v) 8 /\ (1 <= p_w v)%Z /\ (1 <= p_h v)%Z /\ p_wpl v = wpl_of (p_w v) 8 /\
  live A (Z_to_bv 64 pixs) = Some 64%Z /\ live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z /\
  p_xres v = 0%Z /\ p_yres v = 0%Z.   (* [comment removed for export] *)

Definition pixAddMirroredBorder_contract : Prop :=
  forall C A m md regs (s pixs b : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + AMB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 b -> getr regs 12 = Z_to_bv 64 b -> getr regs 13 = Z_to_bv 64 b -> getr regs 14 = Z_to_bv 64 b ->
  bl_src A m pixs v -> (b = 11 \/ b = 20)%Z -> (b <= p_w v)%Z -> (b <= p_h v)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_amb (p_w v) (p_h v) b <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd data, getr regs' 10 = Z_to_bv 64 pixd /\ hdr_ok (p_w v + 2 * b) (p_h v + 2 * b) 8 /\
                            pixr_new C A A' m' pixd data (set_data (pix_hdr (p_w v + 2 * b) (p_h v + 2 * b) 8) data))) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_amb (p_w v) (p_h v) b) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixAddMirroredBorder) m al_rom) md) S.

Definition pixGetExtremeValue_contract : Prop :=
  forall C A m md regs (s pixs typ cellp : Z) (v : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GEV_STACK <= s)%Z -> (s <= cellp)%Z -> (cellp + 4 <= c_top C)%Z -> (cellp mod 4 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 typ -> getr regs 13 = Z_to_bv 64 0 -> getr regs 14 = Z_to_bv 64 0 ->
  getr regs 15 = Z_to_bv 64 0 -> getr regs 16 = Z_to_bv 64 cellp ->
  bl_src A m pixs v -> (typ = 4 \/ typ = 5)%Z ->
  (forall m' regs' (val : Z), W C A m' md -> cs_kept regs regs' ->
     (0 <= val <= 255)%Z -> rdn SEGS m' (Z_to_bv 64 cellp) 4 = Some (Z_to_le_bytes 4 val) ->
     (forall a : word, ~ scratch C s a -> ~ (cellp <= u a < cellp + 4)%Z -> m' a = m a) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixGetExtremeValue) m al_rom) md) S.
End BlIface.
