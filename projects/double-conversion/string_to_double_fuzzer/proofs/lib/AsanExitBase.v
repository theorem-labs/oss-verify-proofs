(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgA.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim LibAtomic ExitSim ShapeAlg Nodes.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AsanAcct AsanAcctImages.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export SumWalkTac.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Export AsanAcctNoLazy.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := ImgA.M.loaded_segments.

Definition Asan_wx_nowrap' : wx_segs_nowrap ASEGS := Asan_wx_nowrap.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asan_wseg_wd1 : wseg_ok ASEGS (0x12e590 : word) 1016%nat = true.
Proof. vm_compute. reflexivity. Qed.

Lemma store_ok_data1 : forall m (a : word) n,
  (0x12e590 <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= 0x12e988)%Z ->
  store_ok ASEGS m a n = true.
Proof.
  intros m a n Hlo Hhi.
  eapply (store_ok_window ASEGS m (0x12e590 : word) a 1016%nat n 0x12e590 0x12e988);
    [reflexivity | reflexivity | lia | exact asan_wseg_wd1 | exact Hlo | exact Hhi].
Qed.

(* [comment removed for export] *)
Ltac sok_data := store_ok_peel; apply store_ok_data1; zsimp; lia.

(* [comment removed for export] *)
Ltac sok_frame SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 112%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma asan_window_data : window_in_seg_b ASEGS 0x12b000 0x688000 = true.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_window_got : window_in_seg_b ASEGS 0x124000 0x12b000 = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma data_avoids : forall H (a : Z) n,
  H_off_segments ASEGS H ->
  (0x12b000 <= a)%Z -> (a + Z.of_nat n <= 0x688000)%Z ->
  range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros H a n HH Hlo Hhi.
  apply (range_avoids_in_window ASEGS H 0x12b000 0x688000 a n HH asan_window_data); lia.
Qed.

(* [comment removed for export] *)
Lemma got_avoids : forall H (a : Z) n,
  H_off_segments ASEGS H ->
  (0x124000 <= a)%Z -> (a + Z.of_nat n <= 0x12b000)%Z ->
  range_avoids H (Z_to_bv 64 a) n.
Proof.
  intros H a n HH Hlo Hhi.
  apply (range_avoids_in_window ASEGS H 0x124000 0x12b000 a n HH asan_window_got); lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_mrestrict_data : forall H mem (a : Z) n bs,
  H_off_segments ASEGS H ->
  (0x12b000 <= a)%Z -> (a + Z.of_nat n <= 0x688000)%Z ->
  rdn ASEGS mem (Z_to_bv 64 a) n = Some bs ->
  rdn ASEGS (mrestrict H mem) (Z_to_bv 64 a) n = Some bs.
Proof.
  intros H mem a n bs HH Hlo Hhi Hr. rewrite (rdn_mrestrict_eq ASEGS H); [exact Hr|].
  apply data_avoids; assumption.
Qed.

Lemma rdn_mrestrict_got : forall H mem (a : Z) n bs,
  H_off_segments ASEGS H ->
  (0x124000 <= a)%Z -> (a + Z.of_nat n <= 0x12b000)%Z ->
  rdn ASEGS mem (Z_to_bv 64 a) n = Some bs ->
  rdn ASEGS (mrestrict H mem) (Z_to_bv 64 a) n = Some bs.
Proof.
  intros H mem a n bs HH Hlo Hhi Hr. rewrite (rdn_mrestrict_eq ASEGS H); [exact Hr|].
  apply got_avoids; assumption.
Qed.

(* [comment removed for export] *)
Lemma rdn_mrestrict_av : forall H mem (a : word) n bs,
  range_avoids H a n ->
  rdn ASEGS mem a n = Some bs ->
  rdn ASEGS (mrestrict H mem) a n = Some bs.
Proof. intros H mem a n bs Hav Hr. rewrite (rdn_mrestrict_eq ASEGS H); assumption. Qed.

Lemma store_ok_mrestrict_av : forall H mem (a : word) n,
  range_avoids H a n ->
  store_ok ASEGS mem a n = true ->
  store_ok ASEGS (mrestrict H mem) a n = true.
Proof. intros H mem a n Hav Hs. rewrite (store_ok_mrestrict_eq ASEGS H); assumption. Qed.

(* [comment removed for export] *)
Lemma range_avoids_subZ : forall H (z : Z) n (b : Z) k,
  range_avoids H (Z_to_bv 64 z) n ->
  (0 <= z < 2 ^ 64)%Z ->
  (z <= b)%Z -> (b + Z.of_nat k <= z + Z.of_nat n)%Z ->
  range_avoids H (Z_to_bv 64 b) k.
Proof.
  intros H z n b k Hr Hz Hlo Hhi.
  apply (range_avoids_sub H (Z_to_bv 64 z) n b k Hr); rewrite u_Z2bv by lia; lia.
Qed.


Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
