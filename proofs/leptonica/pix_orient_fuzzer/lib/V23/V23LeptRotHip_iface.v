(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib LeptDefs LeptStructs.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition HIP_STACK : Z := 240.   (* [comment removed for export] *)
Definition PC_rasteropHipLow : Z := 0x875f4.

Section HipIface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition rasteropHipLow_contract : Prop :=
  forall C Ar A m md regs (s data h wpl shift kd : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + HIP_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 data -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 wpl ->
  getr regs 14 = Z_to_bv 64 0 -> getr regs 15 = Z_to_bv 64 h -> getr regs 16 = Z_to_bv 64 shift ->
  (0 <= data < 2 ^ 64)%Z -> (1 <= shift <= 31)%Z -> (1 <= wpl)%Z -> (1 <= h)%Z -> (4 * (wpl * h) <= 67108864)%Z ->
  live A (Z_to_bv 64 data) = Some kd -> (4 * (wpl * h) <= kd)%Z -> live Ar (Z_to_bv 64 data) = None -> live (c_A0 C) (Z_to_bv 64 data) = None ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     (forall a : word, ~ scratch C s a -> ~ (data <= u a < data + 4 * (wpl * h))%Z -> m' a = m a) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropHipLow) m al_rom) md) S.

End HipIface.
