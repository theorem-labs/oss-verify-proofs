(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
From OSSVerify.coturn.FuzzStunClient.images Require Import
  Asan AsanUbsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition Src_0_top : Z := 0x58000%Z.   (* [comment removed for export] *)
Lemma Src_0_wx_nowrap : wx_segs_nowrap Plain_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Src_0_segs_below : segs_below_b Plain_loaded_segments Src_0_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Src_0_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Src_0_top <= bv_unsigned a)%Z) ->
  H_off_segments Plain_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Src_0_segs_below Ha). Qed.
Lemma Src_0_H_off_mkH : forall L A,
  ranges_from_b L Src_0_top = true -> H_off_segments Plain_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Src_0_segs_below HL). Qed.

(* [comment removed for export] *)
Definition Asan_top : Z := 0x608000%Z.
Lemma Asan_wx_nowrap : wx_segs_nowrap Asan_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan_segs_below : segs_below_b Asan_loaded_segments Asan_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Asan_top <= bv_unsigned a)%Z) ->
  H_off_segments Asan_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan_segs_below Ha). Qed.
Lemma Asan_H_off_mkH : forall L A,
  ranges_from_b L Asan_top = true ->
  H_off_segments Asan_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan_segs_below HL). Qed.

(* [comment removed for export] *)
Definition Both_top : Z := 0x607000%Z.
Lemma Both_wx_nowrap : wx_segs_nowrap AsanUbsan_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Both_segs_below : segs_below_b AsanUbsan_loaded_segments Both_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Both_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Both_top <= bv_unsigned a)%Z) ->
  H_off_segments AsanUbsan_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Both_segs_below Ha). Qed.
Lemma Both_H_off_mkH : forall L A,
  ranges_from_b L Both_top = true ->
  H_off_segments AsanUbsan_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Both_segs_below HL). Qed.

