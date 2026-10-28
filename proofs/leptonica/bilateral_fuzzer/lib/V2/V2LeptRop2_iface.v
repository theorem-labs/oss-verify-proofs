(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptBase V2LeptRop_iface.
Import ListNotations.
Open Scope bv_scope.

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition rop2_arm (DX SX DW swpl : Z) : Prop :=
  (DX mod 32 = 0 /\ SX mod 32 = 0)%Z \/ (DX mod 32 <> SX mod 32 /\ g_smax DX SX DW <= swpl - 1)%Z.

(* [comment removed for export] *)
Definition ROPN_STACK : Z := 16 + LSF.

Section Rop2Iface.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition rasteropLow_arm_contract (ARM : Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall C Ar A m md regs (s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPLOW_STACK <= s)%Z -> (s + 64 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 datad -> getr regs 11 = Z_to_bv 64 dpixw -> getr regs 12 = Z_to_bv 64 dpixh -> getr regs 13 = Z_to_bv 64 d ->
  getr regs 14 = Z_to_bv 64 dwpl -> getr regs 15 = Z_to_bv 64 dx -> getr regs 16 = Z_to_bv 64 dy -> getr regs 17 = Z_to_bv 64 dw ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 12)) ->
  rdn SEGS m (Z_to_bv 64 (s + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 datas)) ->
  rdn SEGS m (Z_to_bv 64 (s + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixw)) ->
  rdn SEGS m (Z_to_bv 64 (s + 32)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spixh)) ->
  rdn SEGS m (Z_to_bv 64 (s + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) ->
  rdn SEGS m (Z_to_bv 64 (s + 48)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sx)) ->
  rdn SEGS m (Z_to_bv 64 (s + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  (0 <= datad < 2 ^ 64)%Z -> (0 <= datas < 2 ^ 64)%Z ->
  rop_shape dpixw dpixh d dwpl -> rop_shape spixw spixh d swpl ->
  rop_rect dpixw dpixh dx dy dw dh -> rop_rect spixw spixh sx sy dw dh ->
  ARM (dx * d)%Z (sx * d)%Z (dw * d)%Z swpl ->
  live A (Z_to_bv 64 datad) = Some (4 * (dwpl * dpixh))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datas) = Some (4 * (swpl * spixh))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
      (forall a : word, ~ scratch C s a -> ~ (datad <= bv_unsigned a < datad + 4 * (dwpl * dpixh))%Z -> m' a = m a) ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_rasteropLow) m al_rom) md) S.

Definition rasteropLow_gen_contract : Prop :=
  rasteropLow_arm_contract (fun DX SX DW swpl => DX mod 32 <> SX mod 32 /\ g_smax DX SX DW <= swpl - 1)%Z.
Definition rasteropLow_al_contract : Prop :=
  rasteropLow_arm_contract (fun DX SX DW swpl => DX mod 32 = 0 /\ SX mod 32 = 0)%Z.
Definition rasteropLow2_contract : Prop := rasteropLow_arm_contract rop2_arm.

(* [comment removed for export] *)
Definition pixRasterop_src2_contract : Prop :=
  forall C Ar A m md regs (s pixd dx dy dw dh pixs sx sy : Z) (vd vs : pixv) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROP_STACK <= s)%Z -> (s + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 dx -> getr regs 12 = Z_to_bv 64 dy -> getr regs 13 = Z_to_bv 64 dw ->
  getr regs 14 = Z_to_bv 64 dh -> getr regs 15 = Z_to_bv 64 12 -> getr regs 16 = Z_to_bv 64 pixs -> getr regs 17 = Z_to_bv 64 sx ->
  rdn SEGS m (Z_to_bv 64 s) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 sy)) ->
  PIXat m pixd vd -> PIXat m pixs vs -> p_d vs = p_d vd ->
  rop_shape (p_w vd) (p_h vd) (p_d vd) (p_wpl vd) -> rop_shape (p_w vs) (p_h vs) (p_d vs) (p_wpl vs) ->
  rop_rect (p_w vd) (p_h vd) dx dy dw dh -> rop_rect (p_w vs) (p_h vs) sx sy dw dh ->
  rop2_arm (dx * p_d vd)%Z (sx * p_d vd)%Z (dw * p_d vd)%Z (p_wpl vs) ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  Z_to_bv 64 pixd <> Z_to_bv 64 (p_data vd) -> Z_to_bv 64 pixs <> Z_to_bv 64 (p_data vd) ->
  live A (Z_to_bv 64 (p_data vd)) = Some (4 * (p_wpl vd * p_h vd))%Z -> live Ar (Z_to_bv 64 (p_data vd)) = None ->
  live (c_A0 C) (Z_to_bv 64 (p_data vd)) = None ->
  live A (Z_to_bv 64 (p_data vs)) = Some (4 * (p_wpl vs * p_h vs))%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' -> PIXat m' pixd vd -> PIXat m' pixs vs ->
      getr regs' 10 = Z_to_bv 64 0 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixRasterop_null_contract : Prop :=
  forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + ROPN_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' ->
      (forall a : word, ~ scratch C s a -> m' a = m a) -> mem_grows m m' ->
      getr regs' 10 = Z_to_bv 64 1 ->
      realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_pixRasterop) m al_rom) md) S.

End Rop2Iface.
