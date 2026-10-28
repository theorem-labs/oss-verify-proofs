(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import AsanAcct.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition Asan_top : Z := 0x6ce000%Z.
Lemma Asan_wx_nowrap : wx_segs_nowrap AsanUbsan_loaded_segments.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.
Lemma Asan_segs_below : segs_below_b AsanUbsan_loaded_segments Asan_top = true.
Proof. vm_compute. reflexivity. Qed.
Lemma Asan_H_off_above : forall H : word -> bool,
  (forall a, H a = true -> (Asan_top <= bv_unsigned a)%Z) ->
  H_off_segments AsanUbsan_loaded_segments H.
Proof. intros H Ha. exact (H_off_segments_above _ H _ Asan_segs_below Ha). Qed.
Lemma Asan_H_off_mkH : forall L A,
  ranges_from_b L Asan_top = true ->
  H_off_segments AsanUbsan_loaded_segments (mkH L A).
Proof. intros L A HL. exact (H_off_segments_mkH _ L A _ Asan_segs_below HL). Qed.
