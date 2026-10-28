(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Bs0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BBytes BZBridge BacX BSFModel BSysStep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BStrFun.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface B5_smkit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma land_16383 : forall x, Z.land x 16383 = x mod 16384.
Proof. intros. change 16383 with (Z.ones 14). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_2047 : forall x, Z.land x 2047 = x mod 2048.
Proof. intros. change 2047 with (Z.ones 11). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_511 : forall x, Z.land x 511 = x mod 512.
Proof. intros. change 511 with (Z.ones 9). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_255 : forall x, Z.land x 255 = x mod 256.
Proof. intros. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_63 : forall x, Z.land x 63 = x mod 64.
Proof. intros. change 63 with (Z.ones 6). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma wrap_mod_16384 : forall e, bv_unsigned (Z_to_bv 64 e) mod 16384 = e mod 16384.
Proof. intros e. exact (unsigned_wrap_mod e 14 ltac:(lia)). Qed.
Lemma wrap_mod_4096 : forall e, bv_unsigned (Z_to_bv 64 e) mod 4096 = e mod 4096.
Proof. intros e. exact (unsigned_wrap_mod e 12 ltac:(lia)). Qed.
Lemma wrap_mod_2048 : forall e, bv_unsigned (Z_to_bv 64 e) mod 2048 = e mod 2048.
Proof. intros e. exact (unsigned_wrap_mod e 11 ltac:(lia)). Qed.
Lemma wrap_mod_512 : forall e, bv_unsigned (Z_to_bv 64 e) mod 512 = e mod 512.
Proof. intros e. exact (unsigned_wrap_mod e 9 ltac:(lia)). Qed.
Lemma wrap_mod_256 : forall e, bv_unsigned (Z_to_bv 64 e) mod 256 = e mod 256.
Proof. intros e. exact (unsigned_wrap_mod e 8 ltac:(lia)). Qed.
Lemma wrap_mod_64 : forall e, bv_unsigned (Z_to_bv 64 e) mod 64 = e mod 64.
Proof. intros e. exact (unsigned_wrap_mod e 6 ltac:(lia)). Qed.

Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (b8 0) 8.
Proof. vm_compute. reflexivity. Qed.
Lemma cells_bytes_zero_words : forall n, cells_bytes (repeat (C8 (Z_to_bv 64 0)) n) = repeat (b8 0) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes]. rewrite IH, le8_zero.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.
Lemma cells_size_zero_words : forall n, cells_size (repeat (C8 (Z_to_bv 64 0)) n) = (8 * n)%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_size csize]. rewrite IH. lia. Qed.

Lemma shad_of_zero_words : forall (n : nat) m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0)) n) -> SHAD m A (poison_bytes (8 * n) 0).
Proof.
  intros n m A H0 H8 [[WF BA] WR]. split; [exact H0|]. split; [exact H8|]. unfold poison_bytes. split.
  - rewrite <- cells_bytes_zero_words. exact BA.
  - rewrite repeat_length, <- cells_size_zero_words. exact WR.
Qed.

Lemma shad8_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) [C8 (Z_to_bv 64 0)] -> SHAD m A (poison_bytes 8 0).
Proof. intros m A H0 H8 RC. exact (shad_of_zero_words 1 m A H0 H8 RC). Qed.
Lemma shad32_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0)) 4) -> SHAD m A (poison_bytes 32 0).
Proof. intros m A H0 H8 RC. exact (shad_of_zero_words 4 m A H0 H8 RC). Qed.
Lemma shad64_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0)) 8) -> SHAD m A (poison_bytes 64 0).
Proof. intros m A H0 H8 RC. exact (shad_of_zero_words 8 m A H0 H8 RC). Qed.
Lemma shad256_of_words : forall m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 0)) 32) -> SHAD m A (poison_bytes 256 0).
Proof. intros m A H0 H8 RC. exact (shad_of_zero_words 32 m A H0 H8 RC). Qed.

Lemma le8_f5 : le8 (Z_to_bv 64 17723342345328784885) = repeat (b8 0xf5) 8.
Proof.
  change (Z_to_bv 64 17723342345328784885) with (Z_to_bv 64 (245 * BC8)). unfold b8. change 0xf5 with 245.
  apply le8_bcast. lia.
Qed.
Lemma cells_bytes_f5_words : forall n, cells_bytes (repeat (C8 (Z_to_bv 64 17723342345328784885)) n) = repeat (b8 0xf5) (8 * n).
Proof.
  induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_bytes cbytes]. rewrite IH, le8_f5.
  replace (8 * S n)%nat with (8 + 8 * n)%nat by lia. rewrite repeat_app. reflexivity.
Qed.
Lemma cells_size_f5_words : forall n, cells_size (repeat (C8 (Z_to_bv 64 17723342345328784885)) n) = (8 * n)%nat.
Proof. induction n as [|n IH]; [reflexivity|]. cbn [repeat cells_size csize]. rewrite IH. lia. Qed.
Lemma shad_of_f5_words : forall (n : nat) m A, 0 <= A -> A mod 8 = 0 ->
  rw_cells asegs m (sh A) (repeat (C8 (Z_to_bv 64 17723342345328784885)) n) -> SHAD m A (poison_bytes (8 * n) 0xf5).
Proof.
  intros n m A H0 H8 [[WF BA] WR]. split; [exact H0|]. split; [exact H8|]. unfold poison_bytes. split.
  - rewrite <- cells_bytes_f5_words. exact BA.
  - rewrite repeat_length, <- cells_size_f5_words. exact WR.
Qed.

Lemma rw_cells_C1_mrd : forall m a b, rw_cells asegs m a [C1 b] -> mrd asegs m (wa a) = Some b.
Proof.
  intros m a b [[_ (_ & _ & B)] _]. specialize (B 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B. exact B.
Qed.

End HCW.
