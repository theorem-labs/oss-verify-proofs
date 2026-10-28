(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomK LeptRoomPC LeptRoomBL LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import FpReal.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptPixHdr V2LeptPixCreate V2LeptPixCopyT V2LeptKernCreateS V2LeptKernDestroyS V2LeptBl_iface V2LeptBl2_iface V2LeptBl3_iface V2LeptKvals.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition RK_bge : Z := (RK_kern 41 + RK_pix + RK_pix + RK_pixcopy)%Z.
(* [comment removed for export] *)
Definition BGE_STACK : Z := 176 + AMB_STACK.
Definition PC_pixBilateralGrayExact : Z := 241016.

Section BgeIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition pixBilateralGrayExact_contract : Prop :=
  forall fr cs C A m md regs (s pixs w h datas skel arrs rkel arrr : Z) (rowss rowsr : Z -> Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BGE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 352880 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 skel -> getr regs 12 = Z_to_bv 64 rkel ->
  PIXat m pixs (hdv w h 8 0 datas) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 8 * h))%Z ->
  kobj C A m skel arrs 41 41 rowss -> korg m skel 20 20 -> kobj C A m rkel arrr 1 256 rowsr ->
  forall (ksf rsf : Z -> Z -> Z), kvals m 41 41 rowss ksf -> ksf 20%Z 20%Z = p_one_s -> kvals m 1 256 rowsr rsf -> rsf 0%Z 0%Z = p_one_s ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_bge <= kR)%Z -> (RB_bge w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 0 -> (forall q, live A' q = live A q) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  (forall fr' cs' A' m' vm' regs' (pixd datad : Z), W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 pixd -> pixr_new C A A' m' pixd datad (set_data (pix_hdr w h 8) datad) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_bge) (bR - RB_bge w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_pixBilateralGrayExact) m al_rom) md) S.
End BgeIface.
