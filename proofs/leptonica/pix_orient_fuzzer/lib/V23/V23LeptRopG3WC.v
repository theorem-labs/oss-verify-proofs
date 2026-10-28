(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptRopClip.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptRop2Segs V23LeptRopGSpec V23LeptRop2WC V23LeptRopGenPre V23LeptRopG3Segs V23LeptRopG3W.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section RopGen3C.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rasteropLow_arm3_clip_contract (ARM : Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 3)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh 1 dwpl -> rop_shape spixw spixh 1 swpl ->
  (- 2 ^ 20 <= dx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sx <= 2 ^ 20)%Z -> (- 2 ^ 20 <= dy <= 2 ^ 20)%Z -> (- 2 ^ 20 <= sy <= 2 ^ 20)%Z ->
  (0 <= dw <= 2 ^ 20)%Z -> (0 <= dh <= 2 ^ 20)%Z ->
  ((1 <= clip_w dx sx dw dpixw spixw)%Z -> (1 <= clip_w dy sy dh dpixh spixh)%Z -> ARM (clip_d dx sx) (clip_s dx sx) (clip_w dx sx dw dpixw spixw) swpl) ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

Definition rasteropLow_gen3_clip_contract : Prop :=
  rasteropLow_arm3_clip_contract (fun DX SX DW swpl => DX mod 32 <> SX mod 32 /\ g_smax DX SX DW <= swpl - 1)%Z.

Lemma jt3g_rd : rdn SEGS (fun _ => None) (Z_to_bv 64 (RG_JT + 4 * (3 - 1))) 4 = Some (Z_to_le_bytes 4 RG3_JTV).
Proof. vm_refl_bv. Qed.

Lemma ent3 : Z_to_bv 64 (RG_JT + RG3_JTV) = RG3_S1.
Proof. apply bv_eq. reflexivity. Qed.

Theorem rasteropLow_gen3_clip_W : rasteropLow_gen3_clip_contract.
Proof.
  exact (rasteropLow_genop_clip_W rg_gen_pre_W 3 RG3_JTV RG3_S1 ltac:(lia) jt3g_rd ent3 ltac:(unfold RG3_JTV; split; [lia | reflexivity]) rg3_loops_W).
Qed.

End RopGen3C.
