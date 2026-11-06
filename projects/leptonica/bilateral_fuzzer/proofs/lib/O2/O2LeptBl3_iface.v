(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRoom LeptRoomK LeptRoomBL LeptExecB.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.O2 Require Import O2LeptBase O2LeptKernCreateS O2LeptKernDestroyS.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Definition KER_STACK : Z := 512 + LSF.
Definition PC_makeGaussianKernel : Z := 184320.
Definition PC_makeRangeKernel : Z := 191392.
Definition PC_kernelInvert : Z := 183956.

(* [comment removed for export] *)
Definition korg (m : word -> option byte) (kel cy cx : Z) : Prop :=
  rdn SEGS m (Z_to_bv 64 (kel + 8)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cy)) /\
  rdn SEGS m (Z_to_bv 64 (kel + 12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cx)).

Section Bl3Iface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Definition makeGaussianKernel_contract : Prop :=
  forall fr cs C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + KER_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 301120 ->
  getr regs 10 = Z_to_bv 64 20 -> getr regs 11 = Z_to_bv 64 20 ->
  reg_get fr 10 = Z_to_bv 64 18446744070507200512 -> reg_get fr 11 = Z_to_bv 64 18446744070479937536 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_kern 41 <= kR)%Z -> (RB_kernS 41 41 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ kern C A A' m' kel arr 41 41 rows /\ korg m' kel 20 20) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_kern 41) (bR - RB_kernS 41 41) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_makeGaussianKernel) m al_rom) md) S.

Definition makeRangeKernel_contract : Prop :=
  forall fr cs C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + KER_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 301120 ->
  reg_get fr 10 = Z_to_bv 64 18446744070479937536 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_kern 1 <= kR)%Z -> (RB_kernS 1 256 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ kern C A A' m' kel arr 1 256 rows /\ korg m' kel 0 0) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_kern 1) (bR - RB_kernS 1 256) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_makeRangeKernel) m al_rom) md) S.

Definition kernelInvert_contract : Prop :=
  forall fr cs C A m md regs (s kels arrs : Z) (rowss : Z -> Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + KER_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 301120 ->
  getr regs 10 = Z_to_bv 64 kels -> kobj C A m kels arrs 41 41 rowss -> korg m kels 20 20 ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_kern 41 <= kR)%Z -> (RB_kernS 41 41 <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' -> cs_kept regs regs' -> POSTM C A s m m' ->
     (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ kern C A A' m' kel arr 41 41 rows /\ korg m' kel 20 20) ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) -> aroom A' vm' (kR - RK_kern 41) (bR - RB_kernS 41 41) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (Z_to_bv 64 PC_kernelInvert) m al_rom) md) S.
End Bl3Iface.
