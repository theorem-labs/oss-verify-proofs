(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomPC LeptRoomBL LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixHdr V2LeptPixCreate V2LeptPixCreateT2 V2LeptPixCopyT.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition RGB_STACK : Z := 1024 + 112 + LSF.   (* [comment removed for export] *)
Definition CRI_STACK : Z := 1024 + 112 + LSF.   (* [comment removed for export] *)
Definition BBE_WIN : Z := 8192.                 (* [comment removed for export] *)
Definition PC_pixGetRGBComponent : Z := 112124.
Definition PC_pixCreateRGBImage : Z := 117472.
Definition PC_pixBlockBilateralExact : Z := 242660.

(* [comment removed for export] *)
Definition RB_bge (w h : Z) : Z := (RB_kernS 41 41 + RB_pixT (4 * (wpl_of (w + 41) 8 * (h + 41))) + RB_pixT (4 * (wpl_of w 8 * h)))%Z.
Definition RB_bbe (w h d : Z) : Z :=
  (if (d =? 8)%Z then RB_kernS 41 41 + RB_kernS 1 256 + RB_bge w h
   else if (d =? 32)%Z then RB_kernS 41 41 + RB_kernS 1 256 + 3 * (RB_pixT (4 * (wpl_of w 8 * h)) + RB_bge w h) + RB_pixT (4 * (wpl_of w 32 * h))
   else 0)%Z.
Definition RK_bbe : Z := 256.      (* [comment removed for export] *)

Section Bl2Iface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition pixGetRGBComponent_contract {fx : FPState} : Prop :=
  forall C A m md regs (s pixs w h datas comp : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RGB_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 comp -> (0 <= comp <= 2)%Z ->
  PIXat m pixs (hdv w h 32 0 datas) -> hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pixT (4 * (wpl_of w 8 * h)) <= bR)%Z ->
  (forall A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of w 8 * h))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixGetRGBComponent) m al_rom) md) S.

(* [comment removed for export] *)
Definition rgb_comp (A : AS) (m : word -> option byte) (r w h : Z) : Prop :=
  r = 0%Z \/ exists dr, PIXat m r (hdv w h 8 0 dr) /\ live A (Z_to_bv 64 r) = Some 64%Z /\ live A (Z_to_bv 64 dr) = Some (4 * (wpl_of w 8 * h))%Z.

Definition pixCreateRGBImage_contract {fx : FPState} : Prop :=
  forall C A m md regs (s pr pg pb w h : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CRI_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pr -> getr regs 11 = Z_to_bv 64 pg -> getr regs 12 = Z_to_bv 64 pb ->
  rgb_comp A m pr w h -> rgb_comp A m pg w h -> rgb_comp A m pb w h -> hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pixT (4 * (wpl_of w 32 * h)) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 32) datad))) ->
     aroom A' vm' (kR - RK_pix) (bR - RB_pixT (4 * (wpl_of w 32 * h))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixCreateRGBImage) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixBlockBilateralExact_contract : Prop :=
  forall fr cs C A m md regs (s pixs w h d cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BBE_WIN <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 -> getr regs 10 = Z_to_bv 64 pixs ->
  reg_get fr 10 = Z_to_bv 64 18446744070507200512 -> reg_get fr 11 = Z_to_bv 64 18446744070479937536 ->
  PIXat m pixs (hdv w h d cm datas) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w d * h))%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bbe <= kR)%Z -> (RB_bbe w h d <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixr_new C A A' m' pixd datad (set_data (pix_hdr w h d) datad))) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bbe) (bR - RB_bbe w h d) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBlockBilateralExact) m al_rom) md) S.
End Bl2Iface.
