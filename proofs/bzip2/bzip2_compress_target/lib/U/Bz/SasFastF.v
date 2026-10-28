(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Arr.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import DecCutF. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import SasFast.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac sas_zb8 :=
  repeat match goal with
  | |- context [length (zb8 _ _)] => rewrite !zb8_length_nat
  | H : context [length (zb8 _ _)] |- _ => rewrite !zb8_length_nat in H
  end.
Ltac sas_zw32 :=
  repeat match goal with
  | |- context [length (zw32 _ _)] => rewrite !zw32_length_nat
  | H : context [length (zw32 _ _)] |- _ => rewrite !zw32_length_nat in H
  end.
Ltac sas_zh16 :=
  repeat match goal with
  | |- context [length (zh16 _ _)] => rewrite !zh16_length_nat
  | H : context [length (zh16 _ _)] |- _ => rewrite !zh16_length_nat in H
  end.

(* [comment removed for export] *)
Ltac sas6F_all := SasFast.sas_u32s; SasFast.sas_u64s; SasFast.sas_upd; sas_zb8; sas_zw32; sas_zh16.

(* [comment removed for export] *)
Local Ltac sasF_selftest hook :=
  intros a n ws i x b v H K; hook;
  lazymatch goal with |- (Z.to_nat n + 4 * Z.to_nat n = Z.to_nat n + length (u32s (zw32 a n)))%nat => idtac end;
  lazymatch type of H with (4 * length ws + Z.to_nat n = v + Z.to_nat n)%nat => idtac end;
  lazymatch goal with v0 := length (zb8 a n) |- _ => idtac end;
  lazymatch type of K with (forall n' : Z, length (zh16 a n') = Z.to_nat n') => idtac end;
  clear H K; rewrite u32s_length, zw32_length_nat; reflexivity.
Goal forall (a : zarr) (n : Z) (ws : list word) (i : nat) (x : word) (b : byte),
  let v := length (zb8 a n) in
  (length (u32s (upd ws i x)) + length (upd (zb8 a n) i b) = v + length (zh16 a n))%nat ->
  (forall n' : Z, length (zh16 a n') = Z.to_nat n') ->
  (length (zb8 a n) + length (u32s (zw32 a n)) = length (zh16 a n) + length (upd (u32s (zw32 a n)) i b))%nat.
Proof. sasF_selftest ltac:(rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zb8_length_nat, ?zw32_length_nat, ?zh16_length_nat in *). Qed.
Goal forall (a : zarr) (n : Z) (ws : list word) (i : nat) (x : word) (b : byte),
  let v := length (zb8 a n) in
  (length (u32s (upd ws i x)) + length (upd (zb8 a n) i b) = v + length (zh16 a n))%nat ->
  (forall n' : Z, length (zh16 a n') = Z.to_nat n') ->
  (length (zb8 a n) + length (u32s (zw32 a n)) = length (zh16 a n) + length (upd (u32s (zw32 a n)) i b))%nat.
Proof. sasF_selftest sas6F_all. Qed.
